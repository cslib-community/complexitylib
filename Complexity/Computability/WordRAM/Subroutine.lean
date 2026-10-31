/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Dynamic
public import Complexity.Computability.WordRAM.Heap
public import Complexity.Computability.WordRAM.MapOp
public import Complexity.Foundations.Semantics.Stateful.Amortized

/-!
# Composable Word-RAM data-structure subroutines

This file unifies standalone Word-RAM data-structure realizations (`DynamicProgram`,
`DynamicCertificate`, `Stateful.Amortized`, `Stateful.Bound`) with inline subroutine composition
inside structured outer algorithms (`Code.rename`, `ExecWithin`).

A data structure is packaged once as a `SubroutineCode B r_ds k_init` and certified by a
`SubroutineDS` bundle. From that single proof, this file derives:

1. **Defined-evaluation basis lifting (`SubroutineCode.mapSimulates`, `SubroutineDS.mapSimulates`,
   `SubroutineDS.toStandard`):** Non-faulting executions over `Basis.exact` lift
   instruction-for-instruction to `Basis.standard` via `Basis.Simulates.exactStandard` from
   `Complexity.Computability.WordRAM.MapOp`, bridging exact-basis algorithms and standard-basis
   `DynamicProgram` realizations.
2. **Standalone `Stateful` projections:** `toDynamicProgram`, `toCertificate`, `toAmortized`,
   `toBound`, and adaptive-client corollaries.
3. **Relocated initialization (`initFresh_rename`, `initClear_rename`):** Both `O(1)` fresh
   initialization on zeroed `Data.init` memory and generic `O(space)` dirty-memory re-initialization
   along any injective register embedding `f : Fin r_ds → Fin r_caller`.
4. **Relocated inline calls and bidirectional framing (`call_rename`, `frame_caller`):** Inline
   execution with amortized potential accounting, DS-to-caller `Modifies` framing, and caller-to-DS
   representation/potential framing.
5. **Potential-retaining loop rule (`ExecWithin.loop_potential_retain`):** Retains exit potential
   `+ Φ z` across inner loops so stored data-structure credit survives nested loops.

## Main definitions

* `Cslib.WordRAM.SubroutineCode`, `Cslib.WordRAM.SubroutineBase`, `Cslib.WordRAM.SubroutineDS`:
  uniform relocatable machine code, step-independent initialization/framing bundle, and unified
  standalone / inline specification and resource certificate for a Word-RAM data structure.
* `Cslib.WordRAM.SubroutineCode.initFresh`, `Cslib.WordRAM.SubroutineCode.initClear`: `O(1)` fresh
  initialization on zeroed memory and generic `O(space)` dirty-memory re-initialization.
* `Cslib.WordRAM.SubroutineCode.toDynamicProgram`, `Cslib.WordRAM.SubroutineDS.toCertificate`:
  standalone `.standard`-basis `DynamicProgram` and `DynamicCertificate` projections.

## Main results

* `Cslib.WordRAM.ExecWithin.loop_potential_retain`: potential-retaining loop rule for nested loops.
* `Cslib.WordRAM.SubroutineDS.toAmortized`, `Cslib.WordRAM.SubroutineDS.toBound`,
  `Cslib.WordRAM.SubroutineDS.run_client_amortized`, `Cslib.WordRAM.SubroutineDS.run_client_bound`:
  standalone amortized and worst-case instruction bounds over `Basis.standard`.
* `Cslib.WordRAM.SubroutineBase.initFresh_rename`, `Cslib.WordRAM.SubroutineBase.initClear_rename`,
  `Cslib.WordRAM.SubroutineDS.call_rename`, `Cslib.WordRAM.SubroutineBase.frame_caller`: relocated
  inline initialization, inline operation calls, and bidirectional register/memory framing.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 17][CLRS2009]
* [J. C. Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures*][Reynolds2002]
-/

@[expose] public section

namespace Cslib.WordRAM

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

/-- Registers outside `Set.range f` retain their caller values under `Data.extend`. -/
theorem Data.extend_regs_of_notMem {r r' : ℕ} {f : Fin r → Fin r'} (y : Data r) (x : Data r')
    {j : Fin r'} (hj : j ∉ Set.range f) : (y.extend f x).regs j = x.regs j :=
  Function.extend_apply' _ _ _ hj

/-- `Data.extend` preserves memory. -/
@[simp]
theorem Data.extend_mem {r r' : ℕ} (f : Fin r → Fin r') (y : Data r) (x : Data r') :
    (y.extend f x).mem = y.mem := rfl

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

/-! ## `SubroutineCode` and `SubroutineDS` -/

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

/-- `O(1)` initializer when `[frontier, frontier + space)` is already zeroed (e.g. `Data.init`). -/
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

/-- Generic `O(space)` reusable initializer on arbitrary dirty memory (`zeroFillCode` +
`initSetup`). -/
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

/-- Project subroutine code and its calling convention to the same operation signature.
The basis is retained, so this projection does not translate instructions or resource claims. -/
def toDynamicProgram (P : SubroutineCode B r_ds k_init) {O : Type*} {Result : O → Type*}
    (encode : O → Fin r_ds → ℕ) (decode : (o : O) → (Fin r_ds → ℕ) → Option (Result o)) :
    DynamicProgram ⟨O, Result⟩ r_ds B where
  code := P.code
  output := P.output
  input := P.input
  encode := encode
  decode := decode

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
  have hfit0 : Fits w 0 := (hx₁.1 P.baseReg).of_le (Nat.zero_le _)
  have hfit_stop : Fits w (base + space) := hfr₁ ▸ hx₁.1 P.frontierReg
  obtain ⟨hcur_not, hzero_not, hone_not, hbase_ne_fr, _⟩ :=
    (List.nodup_cons.mp hclear).imp_right fun h =>
      (List.nodup_cons.mp h).imp_right fun h =>
        (List.nodup_cons.mp h).imp_right List.nodup_cons.mp
  have hcur_ne_zero : P.curReg ≠ P.zeroReg := fun h => hcur_not (by simp [h])
  have hcur_ne_one : P.curReg ≠ P.oneReg := fun h => hcur_not (by simp [h])
  have hcur_ne_base : P.curReg ≠ P.baseReg := fun h => hcur_not (by simp [h])
  have hcur_ne_fr : P.curReg ≠ P.frontierReg := fun h => hcur_not (by simp [h])
  have hzero_ne_one : P.zeroReg ≠ P.oneReg := fun h => hzero_not (by simp [h])
  have hzero_ne_base : P.zeroReg ≠ P.baseReg := fun h => hzero_not (by simp [h])
  have hzero_ne_fr : P.zeroReg ≠ P.frontierReg := fun h => hzero_not (by simp [h])
  have hone_ne_base : P.oneReg ≠ P.baseReg := fun h => hone_not (by simp [h])
  have hone_ne_fr : P.oneReg ≠ P.frontierReg := fun h => hone_not (by simp [h])
  by_cases hsp : 0 < space
  · have hc_pos : (Cond.lt P.baseReg P.frontierReg).Holds x₁ := by
      simp only [Cond.Holds, hb₁, hfr₁]
      omega
    have hfit1 : Fits w 1 := hfit_stop.of_le (by omega)
    let x_z := x₁.set P.zeroReg 0
    let x_o := x_z.set P.oneReg 1
    let x_c := x_o.set P.curReg (x_o.regs P.baseReg)
    have hxc_base : x_c.regs P.baseReg = base := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hcur_ne_base.symm,
        Function.update_of_ne hone_ne_base.symm, Function.update_of_ne hzero_ne_base.symm, hb₁]
    have hxc_fr : x_c.regs P.frontierReg = base + space := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hcur_ne_fr.symm,
        Function.update_of_ne hone_ne_fr.symm, Function.update_of_ne hzero_ne_fr.symm, hfr₁]
    have hxc_zero : x_c.regs P.zeroReg = 0 := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hcur_ne_zero.symm,
        Function.update_of_ne hzero_ne_one]
    have hxc_one : x_c.regs P.oneReg = 1 := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hcur_ne_one.symm]
    have hxc_cur : x_c.regs P.curReg = base := by
      simp [x_c, x_o, x_z, Data.set, Function.update_of_ne hone_ne_base.symm,
        Function.update_of_ne hzero_ne_base.symm, hb₁]
    let xs : ℕ → Data r_ds := fun i =>
      ⟨Function.update x_c.regs P.curReg (base + i), clear x₁.mem base i⟩
    have hxs0 : xs 0 = x_c := by
      ext r
      · by_cases hr : r = P.curReg
        · subst hr
          simp [xs, hxc_cur]
        · simp [xs, Function.update_of_ne hr, x_c, x_o, x_z, Data.set]
      · simp [xs, x_c, x_o, x_z, Data.set]
    have hloop_cond : ∀ i < space, (Cond.lt P.curReg P.frontierReg).Holds (xs i) := by
      intro i hi
      simp only [Cond.Holds, xs, Function.update_self,
        Function.update_of_ne hcur_ne_fr.symm, hxc_fr]
      omega
    have hloop_exit : ¬(Cond.lt P.curReg P.frontierReg).Holds (xs space) := by
      simp only [Cond.Holds, xs, Function.update_self,
        Function.update_of_ne hcur_ne_fr.symm, hxc_fr]
      omega
    have hloop_body : ∀ i < space,
        ExecWithin w (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur))
          (xs i) (xs (i + 1)) 2 := by
      intro i hi
      have hsi_zero : (xs i).regs P.zeroReg = 0 := by
        simp [xs, Function.update_of_ne hcur_ne_zero.symm, hxc_zero]
      have hsi_one : (xs i).regs P.oneReg = 1 := by
        simp [xs, Function.update_of_ne hcur_ne_one.symm, hxc_one]
      have hsi_cur : (xs i).regs P.curReg = base + i := by simp [xs]
      let x_st := (xs i).write ((xs i).regs P.curReg) ((xs i).regs P.zeroReg)
      have hst_one : x_st.regs P.oneReg = 1 := hsi_one
      have hst_fit : Fits w (x_st.regs P.curReg + 1) := by
        change Fits w ((xs i).regs P.curReg + 1)
        rw [hsi_cur]
        exact hfit_stop.of_le (by omega)
      have hinc : ExecWithin w (.op P.incCur) x_st (x_st.set P.curReg (x_st.regs P.curReg + 1)) 1 :=
        (Exec.op (hinc hst_one hst_fit)).within
      have htarget : x_st.set P.curReg (x_st.regs P.curReg + 1) = xs (i + 1) := by
        ext r
        · simp only [x_st, Data.set, Data.write, xs, hsi_cur]
          by_cases hr : r = P.curReg
          · subst hr
            simp [Nat.add_assoc]
          · simp [Function.update_of_ne hr]
        · simp only [x_st, Data.set, Data.write, hsi_cur, hsi_zero]
          simp [xs, clear_succ]
      rw [htarget] at hinc
      exact ExecWithin.store.seq hinc
    have hloop : ExecWithin w
        (.loop (.lt P.curReg P.frontierReg) (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur)))
        x_c (xs space) (space * (2 + 2) + 2) := by
      simpa [hxs0] using ExecWithin.loop xs space 2 hloop_cond hloop_exit hloop_body
    have hbranch : ExecWithin w P.zeroFillCode x₁ (xs space) (4 * space + 6) := by
      have hseq : ExecWithin w
          (.seq (.op (.const P.zeroReg 0)) <|
           .seq (.op (.const P.oneReg 1)) <|
           .seq (.op (.copy P.curReg P.baseReg)) <|
           .loop (.lt P.curReg P.frontierReg)
             (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur)))
          x₁ (xs space) (3 + (space * 4 + 2)) := by
        obtain ⟨n₁, hn₁, he₁⟩ := (ExecWithin.const (x := x₁) (d := P.zeroReg) hfit0)
        obtain ⟨n₂, hn₂, he₂⟩ := (ExecWithin.const (x := x_z) (d := P.oneReg) hfit1)
        obtain ⟨n₃, hn₃, he₃⟩ := (ExecWithin.copy (B := B) (w := w) (x := x_o)
          (d := P.curReg) (s := P.baseReg))
        obtain ⟨n₄, hn₄, he₄⟩ := hloop
        exact ⟨n₁ + (n₂ + (n₃ + n₄)), by omega, he₁.seq (he₂.seq (he₃.seq he₄))⟩
      exact (ExecWithin.branch_pos hc_pos hseq).mono (by omega)
    refine ⟨xs space, hbranch, hbranch.bounded hx₁, ?_, ?_, ?_, ?_, ?_⟩
    · simp [xs, Function.update_of_ne hcur_ne_base.symm, hxc_base]
    · simp [xs, Function.update_of_ne hcur_ne_fr.symm, hxc_fr]
    · intro j
      have hne := hparams j
      have h1 : P.initParams j ≠ P.curReg := fun h => hne (by simp [h])
      have h2 : P.initParams j ≠ P.zeroReg := fun h => hne (by simp [h])
      have h3 : P.initParams j ≠ P.oneReg := fun h => hne (by simp [h])
      simp [xs, x_c, x_o, x_z, Data.set, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3, hpar₁ j]
    · intro a ha
      exact clear_of_owns (Block.mem_footprint.mp ha)
    · intro a ha
      exact clear_of_not_owns (mt Block.mem_footprint.mpr ha)
  · have hsp0 : space = 0 := by omega
    have hc_neg : ¬(Cond.lt P.baseReg P.frontierReg).Holds x₁ := by
      simp only [Cond.Holds, hb₁, hfr₁, hsp0]
      omega
    have hbranch : ExecWithin w P.zeroFillCode x₁ (x₁.set P.zeroReg 0) (4 * space + 6) :=
      (ExecWithin.branch_neg hc_neg (ExecWithin.const hfit0)).mono (by omega)
    refine ⟨x₁.set P.zeroReg 0, hbranch, hbranch.bounded hx₁, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Data.set, Function.update_of_ne hzero_ne_base.symm, hb₁]
    · simp [Data.set, Function.update_of_ne hzero_ne_fr.symm, hfr₁]
    · intro j
      have hne := hparams j
      have h2 : P.initParams j ≠ P.zeroReg := fun h => hne (by simp [h])
      simp [Data.set, Function.update_of_ne h2, hpar₁ j]
    · intro a ha
      simp [hsp0, Block.footprint] at ha
    · exact Modifies.refl _ _

end SubroutineCode

universe u v z

/-- Step-independent specification, representation, calling-convention, and initialization bundle
for `P : SubroutineCode B r_ds k_init` over a state type `State`, operation type `Op`, observation
family `Result`, and admissibility predicate `valid` at word width `w`, base address `base`,
runtime parameters `params`, and initial state `s₀`.

Extended by `SubroutineDS` so that initialization (`initFresh`, `zeroFillCode`, `initClear`),
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

/-- Project a subroutine bundle to its signature-level program, retaining the instruction basis. -/
def toDynamicProgram (C : SubroutineBase P Result valid w base params s₀) :
    DynamicProgram ⟨O, Result⟩ r_ds B :=
  P.toDynamicProgram C.encode C.decode

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

/-- Relocated `O(1)` fresh initialization along any injective register embedding `f`. -/
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

/-- Relocated `O(space)` dirty-memory initialization along any injective register embedding `f`. -/
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

/-- Compiled flat `Program B r_ds` for `O(1)` fresh zeroed-memory initialization. -/
def initFreshProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.initFresh.program P.output

/-- Compiled flat `Program B r_ds` for `O(space)` dirty-memory reusable initialization. -/
def initClearProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.initClear.program P.output

/-- Compiled flat `Program B r_ds` serving all operations of the data structure. -/
def opProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.code.program P.output

end SubroutineCode

/-- Unified standalone and subroutine specification/resource certificate for
`P : SubroutineCode B r_ds k_init` realizing a relational specification `D : Stateful.Spec` at
word width `w`, base address `base`, runtime parameters `params`, and initial state `s₀`.

Extends `SubroutineBase P D.Result D.valid w base params s₀` (inheriting `toDynamicProgram`,
`initFresh_exec`, `initFresh_rename`, `initClear_exec`, `initClear_rename`,
`frame_caller`, and `prepareRegs`), and existentially quantifies over a permitted outcome
`(s', a)` satisfying `D.step s o s' a` in `step_exec`. -/
structure SubroutineDS {B : Basis} {r_ds k_init : ℕ} (P : SubroutineCode B r_ds k_init)
    (D : Stateful.Spec.{u, v, z}) (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : D.State)
    extends SubroutineBase P D.Result D.valid w base params s₀ where
  /-- Angelic execution of `P.code` for any admissible operation `o` whose arguments match `x.regs`,
  witnessing some permitted outcome `(s', a)` with `D.step s o s' a`. -/
  step_exec : ∀ {s : D.State} {x : Data r_ds} (o : D.Op),
    rep s x → D.valid s o → argMatch o x.regs →
    ∃ y s' a n, Exec w P.code x y n ∧
      D.step s o s' a ∧
      decode o y.regs = some a ∧
      rep s' y ∧
      Modifies (Block.mk base space).footprint x.mem y.mem ∧
      n + potential y ≤ charge s o + potential x

namespace SubroutineDS

variable {B B' : Basis} {r_ds r_caller k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : Stateful.Spec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Construct a `SubroutineDS` for a deterministic specification (`[D.HasStepFn f]`) from a
functional `step_exec` proof at `(D.stepFn s o)`. -/
abbrev ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (space spanTime setupTime initPotential : ℕ)
    (charge : D.State → D.Op → ℕ)
    (rep : D.State → Data r_ds → Prop)
    (potential : Data r_ds → ℕ)
    (encode : D.Op → Fin r_ds → ℕ)
    (argMatch : D.Op → (Fin r_ds → ℕ) → Prop)
    (decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o))
    (bounded : ∀ {s x}, rep s x → x.Bounded w)
    (arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i))
    (encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
      argMatch o (fun i => if P.input i then encode o i else regs i))
    (rep_supported : ∀ {s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) →
      (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
      x'.Bounded w → rep s x → rep s x')
    (potential_supported : ∀ {s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) →
      (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
      rep s x → potential x' = potential x)
    (clear_nodup : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup)
    (params_not_clear : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg])
    (incCur_eval : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
      P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1)))
    (span_exec : ∀ {x : Data r_ds},
      x.Bounded w → x.regs P.frontierReg = base → (∀ j, x.regs (P.initParams j) = params j) →
      ∃ x₁, ExecWithin w P.allocSpan x x₁ spanTime ∧ x₁.mem = x.mem ∧
        x₁.regs P.baseReg = base ∧ x₁.regs P.frontierReg = base + space ∧
        (∀ j, x₁.regs (P.initParams j) = params j))
    (setup_exec : ∀ {x₁ : Data r_ds},
      x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
      (∀ j, x₁.regs (P.initParams j) = params j) →
      (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
      ∃ y, ExecWithin w P.initSetup x₁ y setupTime ∧ y.regs P.frontierReg = base + space ∧
        rep s₀ y ∧ potential y ≤ initPotential ∧
        Modifies (Block.mk base space).footprint x₁.mem y.mem)
    (step_exec : ∀ {s : D.State} {x : Data r_ds} (o : D.Op),
      rep s x → D.valid s o → argMatch o x.regs →
      ∃ y n, Exec w P.code x y n ∧
        decode o y.regs = some (D.stepFn s o).2 ∧
        rep (D.stepFn s o).1 y ∧
        Modifies (Block.mk base space).footprint x.mem y.mem ∧
        n + potential y ≤ charge s o + potential x) :
    SubroutineDS P D w base params s₀ where
  space := space
  spanTime := spanTime
  setupTime := setupTime
  initPotential := initPotential
  charge := charge
  rep := rep
  potential := potential
  encode := encode
  argMatch := argMatch
  decode := decode
  bounded := bounded
  arguments_fit := arguments_fit
  encode_matches := encode_matches
  rep_supported := rep_supported
  potential_supported := potential_supported
  clear_nodup := clear_nodup
  params_not_clear := params_not_clear
  incCur_eval := incCur_eval
  span_exec := span_exec
  setup_exec := setup_exec
  step_exec {s _} o hr hv harg := by
    obtain ⟨y, n, he, hdec, hrep, hmod, hpot⟩ := step_exec o hr hv harg
    exact ⟨y, (D.stepFn s o).1, (D.stepFn s o).2, n, he, D.step_stepFn s o, hdec, hrep, hmod, hpot⟩

/-! ### Projection 1: Basis lifting and standalone `DynamicProgram` / `Stateful` theorems -/

/-- Lift a `SubroutineDS` certificate along any defined-evaluation basis simulation. -/
def mapSimulates (φ : B.Simulates B') (C : SubroutineDS P D w base params s₀) :
    SubroutineDS (P.mapSimulates φ) D w base params s₀ where
  toSubroutineBase := C.toSubroutineBase.mapSimulates φ
  step_exec o hr hv harg :=
    let ⟨y, s', a, n, he, hstep, hdec, hrep, hmod, hpot⟩ := C.step_exec o hr hv harg
    ⟨y, s', a, n, he.mapSimulates φ, hstep, hdec, hrep, hmod, hpot⟩

/-- Lift an exact-basis `SubroutineDS` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : SubroutineDS P D w base params s₀) :
    SubroutineDS P.toStandard D w base params s₀ :=
  C.mapSimulates .exactStandard

section Standard

variable {P_std : SubroutineCode .standard r_ds k_init}
  (C : SubroutineDS P_std D w base params s₀)

/-- Project a `.standard`-basis `SubroutineDS` to a standalone `DynamicCertificate`. -/
def toCertificate : DynamicCertificate (D := D) C.toDynamicProgram w where
  rep := C.rep
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  execute {s x} o hr hv := by
    have hb' : (C.toDynamicProgram.prepare o x).Bounded w :=
      C.toDynamicProgram.prepare_bounded (C.bounded hr) (C.arguments_fit o hv)
    have hr' : C.rep s (C.toDynamicProgram.prepare o x) :=
      C.rep_supported
        (fun i hi => C.toDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hb' hr
    have harg : C.argMatch o (C.toDynamicProgram.prepare o x).regs :=
      C.encode_matches o x.regs
    obtain ⟨y, s', a, n, he, hstep, hdec, hrep, _, _⟩ := C.step_exec o hr' hv harg
    exact ⟨y, s', a, n, he, hstep, hdec, hrep⟩

/-- Project a `.standard`-basis `SubroutineDS` to a standalone `Stateful.Amortized` certificate,
charging `+ 1` per operation for `DynamicProgram`'s trailing `halt` instruction. -/
theorem toAmortized :
    Stateful.Amortized C.toCertificate.realization
      DynamicProgram.OperationTrace.instructions
      (fun _ x => C.potential x)
      (fun s o => C.charge s o + 1) where
  step {s x o a y trace} hr hv he := by
    have hb' : (C.toDynamicProgram.prepare o x).Bounded w :=
      C.toDynamicProgram.prepare_bounded (C.bounded hr) (C.arguments_fit o hv)
    have hr' : C.rep s (C.toDynamicProgram.prepare o x) :=
      C.rep_supported
        (fun i hi => C.toDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hb' hr
    have hp_eq : C.potential (C.toDynamicProgram.prepare o x) = C.potential x :=
      C.potential_supported
        (fun i hi => C.toDynamicProgram.prepare_regs_of_not_input hi o x)
        (fun _ _ => rfl) hr
    have harg : C.argMatch o (C.toDynamicProgram.prepare o x).regs :=
      C.encode_matches o x.regs
    obtain ⟨z, s', a', m, hz, hstep, hdec, hrep, _, hpot⟩ := C.step_exec o hr' hv harg
    obtain ⟨rfl, hinst⟩ := he.eq_of_exec hz
    obtain ⟨_, _, _, ha_trace, _⟩ := he
    have ha_eq : a = a' := Option.some.inj (ha_trace.symm.trans hdec)
    subst ha_eq
    refine ⟨s', hstep, hrep, ?_⟩
    rw [hinst]
    rw [hp_eq] at hpot
    omega

/-- When `C.potential` is identically zero, `SubroutineDS` projects directly to a worst-case
`Stateful.Bound` certificate. -/
theorem toBound (hpot : ∀ x, C.potential x = 0) :
    Stateful.Bound C.toCertificate.realization
      DynamicProgram.OperationTrace.instructions
      (fun s o => C.charge s o + 1) := by
  intro s x o a y trace hr hv he
  obtain ⟨_, _, _, h⟩ := C.toAmortized.step hr hv he
  simp only [hpot] at h
  omega

/-- Standalone adaptive-client amortized bound for any demonically admissible client `p`. -/
theorem run_client_demonic_amortized {α : Type*} (p : D.Client α) {s : D.State} {x : Data r_ds}
    (hr : C.rep s x) (hv : D.DemonicValid s p) :
    ∃ a y traces s' tr,
      Stateful.Executes (C.toDynamicProgram.ExecOp w) p x a y traces ∧
      D.ClientRun s p a s' tr ∧
      C.rep s' y ∧
      traces.length = tr.length ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces + C.potential y ≤
        D.totalCostTranscript (fun s o => C.charge s o + 1) s tr + C.potential x :=
  C.toAmortized.exists_demonic p hr hv

/-- Standalone adaptive-client worst-case bound when `C.potential` is identically zero. -/
theorem run_client_demonic_bound (hpot : ∀ x, C.potential x = 0) {α : Type*} (p : D.Client α)
    {s : D.State} {x : Data r_ds} (hr : C.rep s x) (hv : D.DemonicValid s p) :
    ∃ a y traces s' tr,
      Stateful.Executes (C.toDynamicProgram.ExecOp w) p x a y traces ∧
      D.ClientRun s p a s' tr ∧
      C.rep s' y ∧
      traces.length = tr.length ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        D.totalCostTranscript (fun s o => C.charge s o + 1) s tr :=
  Stateful.Bound.exists_demonic (C.toBound hpot) p hr hv

/-- Standalone adaptive-client amortized bound on a deterministic specification. -/
theorem run_client_amortized
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {α : Type*} (p : D.Client α) {s : D.State} {x : Data r_ds}
    (hr : C.rep s x) (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ y traces,
      Stateful.Executes (C.toDynamicProgram.ExecOp w) p x (D.clientResult s p) y traces ∧
      C.rep (D.clientState s p) y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces + C.potential y ≤
        D.totalCost (fun s o => C.charge s o + 1) s (D.clientHistory s p) + C.potential x :=
  C.toAmortized.exists_executes p hr hv

/-- Standalone adaptive-client worst-case bound on a deterministic specification when
`C.potential` is identically zero. -/
theorem run_client_bound
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (hpot : ∀ x, C.potential x = 0) {α : Type*} (p : D.Client α)
    {s : D.State} {x : Data r_ds} (hr : C.rep s x)
    (hv : D.ValidHistory s (D.clientHistory s p)) :
    ∃ y traces,
      Stateful.Executes (C.toDynamicProgram.ExecOp w) p x (D.clientResult s p) y traces ∧
      C.rep (D.clientState s p) y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        D.totalCost (fun s o => C.charge s o + 1) s (D.clientHistory s p) :=
  Stateful.Bound.exists_executes (C.toBound hpot) p hr hv

end Standard

/-! ### Projection 2: Relocated inline subroutine calls (`code_rename`, `call_rename`) -/

/-- Execute `P.code.rename f` inline when arguments already match `(x.comap f).regs`,
witnessing a permitted outcome `(s', a)` with `D.step s o s' a`. -/
theorem code_rename (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {x : Data r_caller} (o : D.Op)
    (hr : C.rep s (x.comap f)) (hv : D.valid s o) (harg : C.argMatch o (x.comap f).regs) :
    ∃ z s' a t, ExecWithin w (P.code.rename f) x z t ∧
      D.step s o s' a ∧
      C.decode o (z.comap f).regs = some a ∧
      C.rep s' (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤ C.charge s o + C.potential (x.comap f) := by
  obtain ⟨y, s', a, n, he, hstep, hdec, hrep, hmod, hpot⟩ := C.step_exec o hr hv harg
  refine ⟨y.extend f x, s', a, n, (he.rename hf).within, hstep, ?_, ?_, hmod,
    fun j hj => Data.extend_regs_of_notMem y x hj, ?_⟩
  · rw [Data.comap_extend hf]
    exact hdec
  · rw [Data.comap_extend hf]
    exact hrep
  · rw [Data.comap_extend hf]
    exact hpot

/-- Execute `.seq prep (P.code.rename f)` inline after a caller argument-preparation block `prep`
that preserves persistent DS registers and memory in `[base, base + C.space)`. -/
theorem call_rename (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {x x' : Data r_caller} {prep : Code B r_caller} {t_prep : ℕ} (o : D.Op)
    (hr : C.rep s (x.comap f)) (hv : D.valid s o)
    (hprep : ExecWithin w prep x x' t_prep)
    (hb' : (x'.comap f).Bounded w)
    (hreg : ∀ i, P.input i = false → x'.regs (f i) = x.regs (f i))
    (hmem : ∀ a ∈ (Block.mk base C.space).footprint, x'.mem a = x.mem a)
    (harg : C.argMatch o (x'.comap f).regs) :
    ∃ z s' a t, ExecWithin w (.seq prep (P.code.rename f)) x z t ∧
      D.step s o s' a ∧
      C.decode o (z.comap f).regs = some a ∧
      C.rep s' (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x'.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x'.regs j) ∧
      t + C.potential (z.comap f) ≤ t_prep + C.charge s o + C.potential (x.comap f) := by
  have hr' : C.rep s (x'.comap f) :=
    C.rep_supported (x := x.comap f) (x' := x'.comap f) hreg hmem hb' hr
  have hp_eq : C.potential (x'.comap f) = C.potential (x.comap f) :=
    C.potential_supported (x := x.comap f) (x' := x'.comap f) hreg hmem hr
  obtain ⟨z, s', a, t_op, he_op, hstep, hdec, hrep_z, hmod_z, hregs_z, hpot_z⟩ :=
    C.code_rename hf o hr' hv harg
  exact ⟨z, s', a, t_prep + t_op, hprep.seq he_op, hstep, hdec, hrep_z, hmod_z, hregs_z,
    by rw [hp_eq] at hpot_z; omega⟩

/-- Deterministic specialization of `code_rename` for `[D.HasStepFn g]`. -/
theorem code_rename_ofFn
    {g : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn g]
    (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {x : Data r_caller} (o : D.Op)
    (hr : C.rep s (x.comap f)) (hv : D.valid s o) (harg : C.argMatch o (x.comap f).regs) :
    ∃ z t, ExecWithin w (P.code.rename f) x z t ∧
      C.decode o (z.comap f).regs = some (D.stepFn s o).2 ∧
      C.rep (D.stepFn s o).1 (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) ∧
      t + C.potential (z.comap f) ≤ C.charge s o + C.potential (x.comap f) := by
  obtain ⟨z, s', a, t, he, hstep, hdec, hrep, hmod, hregs, hpot⟩ :=
    C.code_rename hf o hr hv harg
  have heq := (D.step_iff_stepFn s o s' a).mp hstep
  have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst heq
  have ha : a = (D.stepFn s o).2 := congrArg Prod.snd heq
  subst hs'; subst ha
  exact ⟨z, t, he, hdec, hrep, hmod, hregs, hpot⟩

/-- Deterministic specialization of `call_rename` for `[D.HasStepFn g]`. -/
theorem call_rename_ofFn
    {g : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn g]
    (C : SubroutineDS P D w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective)
    {s : D.State} {x x' : Data r_caller} {prep : Code B r_caller} {t_prep : ℕ} (o : D.Op)
    (hr : C.rep s (x.comap f)) (hv : D.valid s o)
    (hprep : ExecWithin w prep x x' t_prep)
    (hb' : (x'.comap f).Bounded w)
    (hreg : ∀ i, P.input i = false → x'.regs (f i) = x.regs (f i))
    (hmem : ∀ a ∈ (Block.mk base C.space).footprint, x'.mem a = x.mem a)
    (harg : C.argMatch o (x'.comap f).regs) :
    ∃ z t, ExecWithin w (.seq prep (P.code.rename f)) x z t ∧
      C.decode o (z.comap f).regs = some (D.stepFn s o).2 ∧
      C.rep (D.stepFn s o).1 (z.comap f) ∧
      Modifies (Block.mk base C.space).footprint x'.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x'.regs j) ∧
      t + C.potential (z.comap f) ≤ t_prep + C.charge s o + C.potential (x.comap f) := by
  obtain ⟨z, s', a, t, he, hstep, hdec, hrep, hmod, hregs, hpot⟩ :=
    C.call_rename hf o hr hv hprep hb' hreg hmem harg
  have heq := (D.step_iff_stepFn s o s' a).mp hstep
  have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst heq
  have ha : a = (D.stepFn s o).2 := congrArg Prod.snd heq
  subst hs'; subst ha
  exact ⟨z, t, he, hdec, hrep, hmod, hregs, hpot⟩

/-! ### Projection 3: Flat-program operation-sequence execution (`RunsOps`, `run_ops_exact_*`) -/

/-- Sequential flat-program execution of `ops : List D.Op` by repeated calls to `P.opProg`:
each call prepares input registers via `prepRegs`, runs `P.opProg` from `pc = 0` to `halt`,
decodes a permitted outcome `(s₁, a)` with `D.step s o s₁ a`, modifies memory only within
`[base, base + C.space)`, records the resulting transcript `tr : D.Transcript`, and accumulates
total instructions executed (including each trailing `halt`). -/
inductive RunsOps (C : SubroutineDS P D w base params s₀)
    (prepRegs : D.Op → (Fin r_ds → ℕ) → (Fin r_ds → ℕ) := C.prepareRegs) :
    D.State → Data r_ds → List D.Op → D.Transcript → D.State → Data r_ds → ℕ → Prop
  | nil {s x} : RunsOps C prepRegs s x [] [] s x 0
  | cons {s s₁ s₂ x o a ops tr pc y z steps rest} :
      Runs w P.opProg ⟨0, ⟨prepRegs o x.regs, x.mem⟩⟩ ⟨pc, y⟩ steps →
      (∃ out, step w P.opProg ⟨pc, y⟩ = .halt out) →
      D.step s o s₁ a →
      C.decode o y.regs = some a →
      Modifies (Block.mk base C.space).footprint x.mem y.mem →
      RunsOps C prepRegs s₁ y ops tr s₂ z rest →
      RunsOps C prepRegs s x (o :: ops) (⟨o, a, s₁⟩ :: tr) s₂ z ((steps + 1) + rest)

private theorem step_program_halt (c : Code B r_ds) (out : Fin r_ds) (y : Data r_ds) :
    step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
  step_halt (by
    simp only [Code.program, Nat.zero_add,
      List.getElem?_append_right (Code.length_assemble c 0).le,
      Code.length_assemble, Nat.sub_self, List.getElem?_cons_zero])

/-- Flat-program sequence execution under a custom register-preparation function `prepRegs`. -/
theorem seq_runsOps_of_prep (C : SubroutineDS P D w base params s₀)
    (prepRegs : D.Op → (Fin r_ds → ℕ) → (Fin r_ds → ℕ))
    (hfit : ∀ {s} (o) (regs : Fin r_ds → ℕ), D.valid s o → (∀ i, Fits w (regs i)) →
      ∀ i, Fits w (prepRegs o regs i))
    (hnot_in : ∀ (o : D.Op) (regs : Fin r_ds → ℕ) (i : Fin r_ds),
      P.input i = false → prepRegs o regs i = regs i)
    (harg : ∀ (o : D.Op) (regs : Fin r_ds → ℕ), C.argMatch o (prepRegs o regs)) :
    ∀ (ops : List D.Op) {s : D.State} {x : Data r_ds},
      C.rep s x → D.ValidOpSeq s ops →
      ∃ tr s_fin z t_ops,
        C.RunsOps prepRegs s x ops tr s_fin z t_ops ∧
        tr.ops = ops ∧
        D.ValidTranscript s tr s_fin ∧
        C.rep s_fin z ∧
        t_ops + C.potential z ≤
          D.totalCostTranscript (fun st o => C.charge st o + 1) s tr + C.potential x
  | [], s, x, hr, _ =>
    ⟨[], s, x, 0, .nil, rfl, .nil s, hr, Nat.zero_add (C.potential x) ▸ le_rfl⟩
  | o :: ops, s, x, hr, ⟨hv_o, hv_rest⟩ => by
    let x' : Data r_ds := ⟨prepRegs o x.regs, x.mem⟩
    have hbx := C.bounded hr
    have hb' : x'.Bounded w := ⟨hfit o x.regs hv_o hbx.1, hbx.2⟩
    have hreg' : ∀ i, P.input i = false → x'.regs i = x.regs i :=
      fun i hi => hnot_in o x.regs i hi
    have hr' : C.rep s x' := C.rep_supported hreg' (fun _ _ => rfl) hb' hr
    have hpot' : C.potential x' = C.potential x :=
      C.potential_supported hreg' (fun _ _ => rfl) hr
    obtain ⟨y, s₁, a, m, he_op, hstep, hdec, hr_y, hmod, hpot_m⟩ :=
      C.step_exec o hr' hv_o (harg o x.regs)
    rw [hpot'] at hpot_m
    have hruns : Runs w P.opProg ⟨0, x'⟩ ⟨0 + P.code.size, y⟩ m :=
      he_op.runs (pc := 0) (p := P.opProg) (Program.Contains.self _).append_left
    have hhalt : step w P.opProg ⟨0 + P.code.size, y⟩ = .halt (y.regs P.output) :=
      step_program_halt P.code P.output y
    obtain ⟨tr, s_fin, z, rest, hrest, hops, htr, hr_z, hpot_rest⟩ :=
      seq_runsOps_of_prep C prepRegs hfit hnot_in harg ops hr_y (hv_rest s₁ a hstep)
    refine ⟨⟨o, a, s₁⟩ :: tr, s_fin, z, (m + 1) + rest,
      .cons hruns ⟨_, hhalt⟩ hstep hdec hmod hrest,
      congrArg (o :: ·) hops, .cons _ hv_o hstep htr, hr_z, ?_⟩
    simp only [Stateful.Spec.totalCostTranscript_cons]
    omega

/-- Flat-program sequence execution using `C.prepareRegs`. -/
theorem seq_runsOps (C : SubroutineDS P D w base params s₀)
    (ops : List D.Op) {s : D.State} {x : Data r_ds}
    (hr : C.rep s x) (hv : D.ValidOpSeq s ops) :
    ∃ tr s_fin z t_ops,
      C.RunsOps C.prepareRegs s x ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s tr s_fin ∧
      C.rep s_fin z ∧
      t_ops + C.potential z ≤
        D.totalCostTranscript (fun st o => C.charge st o + 1) s tr + C.potential x := by
  refine C.seq_runsOps_of_prep C.prepareRegs ?_ ?_ C.encode_matches ops hr hv
  · intro s' o regs hv_o hregs i
    simp only [SubroutineBase.prepareRegs]
    split_ifs with hi
    · exact C.arguments_fit o hv_o i hi
    · exact hregs i
  · intro o regs i hi
    simp [SubroutineBase.prepareRegs, hi]

/-- Standalone flat-program operation-sequence theorem with `O(1)` fresh initialization on zeroed
`[base, base + C.space)`. -/
theorem run_ops_exact_fresh (C : SubroutineDS P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hzero : ∀ a ∈ (Block.mk base C.space).footprint, d₀.mem a = 0)
    (ops : List D.Op) (hv : D.ValidOpSeq s₀ ops) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w P.initFreshProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsOps C.prepareRegs s₀ x₀ ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s₀ tr s_fin ∧
      C.rep s_fin z ∧
      t_init ≤ C.initTime ∧
      t_ops + C.potential z ≤
        D.totalCostTranscript (fun st o => C.charge st o + 1) s₀ tr + C.initPotential := by
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ :=
    C.initFresh_exec hd₀ hfr hpar hzero
  have hruns₀ : Runs w P.initFreshProg ⟨0, d₀⟩ ⟨0 + P.initFresh.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := P.initFreshProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w P.initFreshProg ⟨0 + P.initFresh.size, x₀⟩ = .halt (x₀.regs P.output) :=
    step_program_halt P.initFresh P.output x₀
  obtain ⟨tr, s_fin, z, t_ops, hruns_ops, hops, htr, hr_z, hbound⟩ :=
    C.seq_runsOps ops hr₀ hv
  exact ⟨_, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops,
    hops, htr, hr_z, ht_init, by omega⟩

/-- Standalone flat-program operation-sequence theorem with `O(space)` reusable initialization on
arbitrary `w`-bounded memory. -/
theorem run_ops_exact_reusable (C : SubroutineDS P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (ops : List D.Op) (hv : D.ValidOpSeq s₀ ops) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w P.initClearProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsOps C.prepareRegs s₀ x₀ ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s₀ tr s_fin ∧
      C.rep s_fin z ∧
      t_init ≤ C.initTime + 4 * C.space + 6 ∧
      t_ops + C.potential z ≤
        D.totalCostTranscript (fun st o => C.charge st o + 1) s₀ tr + C.initPotential := by
  obtain ⟨x₀, ⟨t_init, ht_init, he_init⟩, _, hr₀, hpot₀, hmod₀⟩ :=
    C.initClear_exec hd₀ hfr hpar
  have hruns₀ : Runs w P.initClearProg ⟨0, d₀⟩ ⟨0 + P.initClear.size, x₀⟩ t_init :=
    he_init.runs (pc := 0) (p := P.initClearProg) (Program.Contains.self _).append_left
  have hhalt₀ : step w P.initClearProg ⟨0 + P.initClear.size, x₀⟩ = .halt (x₀.regs P.output) :=
    step_program_halt P.initClear P.output x₀
  obtain ⟨tr, s_fin, z, t_ops, hruns_ops, hops, htr, hr_z, hbound⟩ :=
    C.seq_runsOps ops hr₀ hv
  exact ⟨_, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, ⟨_, hhalt₀⟩, hmod₀, hruns_ops,
    hops, htr, hr_z, ht_init, by omega⟩

/-- Deterministic specialization of `run_ops_exact_fresh` for `[D.HasStepFn g]`, executing the
canonical transcript `D.canonicalTranscript s₀ ops` to `(D.run s₀ ops).1`. -/
theorem run_ops_exact_fresh_ofFn
    {g : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn g]
    (C : SubroutineDS P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (hzero : ∀ a ∈ (Block.mk base C.space).footprint, d₀.mem a = 0)
    (ops : List D.Op) (hv : D.ValidHistory s₀ ops) :
    ∃ pc₀ x₀ t_init z t_ops,
      Runs w P.initFreshProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsOps C.prepareRegs s₀ x₀ ops
        (D.canonicalTranscript s₀ ops) (D.run s₀ ops).1 z t_ops ∧
      C.rep (D.run s₀ ops).1 z ∧
      t_init ≤ C.initTime ∧
      t_ops + C.potential z ≤
        D.totalCost (fun st o => C.charge st o + 1) s₀ ops + C.initPotential := by
  obtain ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, hhalt₀, hmod₀,
      hruns_ops, hops, htr, hr_z, ht_init, hbound⟩ :=
    C.run_ops_exact_fresh hd₀ hfr hpar hzero ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr hv)
  obtain ⟨_, hs_fin, htr_eq⟩ := (D.validTranscript_iff_run s₀ tr s_fin).mp htr
  rw [hops] at hs_fin htr_eq
  subst hs_fin; subst htr_eq
  rw [D.totalCostTranscript_canonicalTranscript] at hbound
  exact ⟨pc₀, x₀, t_init, z, t_ops, hruns₀, hhalt₀, hmod₀, hruns_ops, hr_z, ht_init, hbound⟩

/-- Deterministic specialization of `run_ops_exact_reusable` for `[D.HasStepFn g]`, executing the
canonical transcript `D.canonicalTranscript s₀ ops` to `(D.run s₀ ops).1`. -/
theorem run_ops_exact_reusable_ofFn
    {g : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn g]
    (C : SubroutineDS P D w base params s₀)
    {d₀ : Data r_ds} (hd₀ : d₀.Bounded w)
    (hfr : d₀.regs P.frontierReg = base)
    (hpar : ∀ j, d₀.regs (P.initParams j) = params j)
    (ops : List D.Op) (hv : D.ValidHistory s₀ ops) :
    ∃ pc₀ x₀ t_init z t_ops,
      Runs w P.initClearProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w P.initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base C.space).footprint d₀.mem x₀.mem ∧
      C.RunsOps C.prepareRegs s₀ x₀ ops
        (D.canonicalTranscript s₀ ops) (D.run s₀ ops).1 z t_ops ∧
      C.rep (D.run s₀ ops).1 z ∧
      t_init ≤ C.initTime + 4 * C.space + 6 ∧
      t_ops + C.potential z ≤
        D.totalCost (fun st o => C.charge st o + 1) s₀ ops + C.initPotential := by
  obtain ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns₀, hhalt₀, hmod₀,
      hruns_ops, hops, htr, hr_z, ht_init, hbound⟩ :=
    C.run_ops_exact_reusable hd₀ hfr hpar ops ((D.validOpSeq_iff_validHistory s₀ ops).mpr hv)
  obtain ⟨_, hs_fin, htr_eq⟩ := (D.validTranscript_iff_run s₀ tr s_fin).mp htr
  rw [hops] at hs_fin htr_eq
  subst hs_fin; subst htr_eq
  rw [D.totalCostTranscript_canonicalTranscript] at hbound
  exact ⟨pc₀, x₀, t_init, z, t_ops, hruns₀, hhalt₀, hmod₀, hruns_ops, hr_z, ht_init, hbound⟩

end SubroutineDS

end Cslib.WordRAM
