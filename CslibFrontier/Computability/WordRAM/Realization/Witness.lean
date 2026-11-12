/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Reindex

/-!
# Retaining a uniform realization witness

`Realizes.Witness` retains supplied scratch, factor and emitter data with the same execution
contract as `Realizes`. Its erasure supplies the existential judgment without discarding the
data used by a concrete backend.

The legacy projections choose one witness of `Realizes` before any runtime argument, width, memory
or register layout. They use classical choice from a proposition: they do not claim executable
extraction from an arbitrary proof. They let adapters refer to the same emitted native code and
its proved exchange factor, without adding another realization judgment.

## Main definitions

* `Realizes.scratchSize`, `Realizes.factor`, `Realizes.code`: select the uniform witness.
* `Realizes.Witness`: retain a specified witness and its execution contract.
* `Realizes.Witness.ofRealizes`: an existential-only choice fallback.
* `Realizes.Witness.consequence`, `Realizes.Witness.consequenceValid`, `Realizes.Witness.congr`,
  `Realizes.Witness.reindex`: the `Realizes` adapters, retaining every supplied field.

## Main results

* `Realizes.code_spec`: the selected code has the complete original realization contract.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.Realizes

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {k l : ℕ}
  {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

/-- A specified realization, retaining its resource parameters and emitter as data. Correctness
is the same contract existentially quantified by `Realizes`, not a new execution semantics. -/
structure Witness (B : Basis) (p : δ → Memory.Prog α) (input : δ ↪ (Fin k → ℕ))
    (output : α ↪ (Fin l → ℕ)) (safe : ℕ → δ → Memory.State → Prop)
    (work : δ → Memory.State → ℕ) where
  /-- Auxiliary registers, excluding results and the reserved extra slot. -/
  scratchSize : ℕ
  /-- Exchange factor for memory charges plus local work. -/
  factor : ℕ
  /-- The emitter, fixed before all runtime values and register placements. -/
  code : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
    (Fin (l + scratchSize + 1) → Fin r) → Code B r
  /-- The existing execution, whole-memory/frontier and register-frame contract. -/
  code_spec : Spec B p input output safe work scratchSize factor code

/-- Forget resource and emitter selection while retaining the original realization judgment. -/
theorem Witness.toRealizes (h : Witness B p input output safe work) :
    Realizes B p input output safe work :=
  ⟨h.scratchSize, h.factor, h.code, h.code_spec⟩

/-- Number of auxiliary registers, chosen independently of every runtime value. -/
noncomputable def scratchSize (h : Realizes B p input output safe work) : ℕ := h.choose

/-- Uniform exchange factor for memory charges plus local work. -/
noncomputable def factor (h : Realizes B p input output safe work) : ℕ := h.choose_spec.choose

/-- One emitter, selected before the register layout or any runtime data. -/
noncomputable def code (h : Realizes B p input output safe work) {r : ℕ} :
    (frontier : Fin r) → (Fin k → Fin r) → (Fin (l + h.scratchSize + 1) → Fin r) → Code B r :=
  h.choose_spec.choose_spec.choose

/-- The selected witness retains width independence, literal whole-memory semantics, all result
coordinates, and the original live-register frame. -/
theorem code_spec (h : Realizes B p input output safe work) {r : ℕ}
    (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + h.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(h.code frontier src tmp).ReadsWidth ∧
    ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
      safe w d (memoryState frontier x) →
      (Memory.spec w).ValidHistory (memoryState frontier x)
        ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
      ∃ y, ExecWithin w (h.code frontier src tmp) x y
          (h.factor * (memoryCost (p d) (memoryState frontier x) +
            work d (memoryState frontier x) + 1)) ∧
        memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (p d) ∧
        (∀ i : Fin l, y.regs (tmp (Fin.castAdd (h.scratchSize + 1) i)) =
          output ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i) ∧
        ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i :=
  h.choose_spec.choose_spec.choose_spec frontier src tmp hi hd hf hs

/-- Select a witness from an existential realization. This fallback preserves correctness but
does not assert concrete scratch, factor or code identities for a particular derivation. -/
noncomputable def Witness.ofRealizes (h : Realizes B p input output safe work) :
    Witness B p input output safe work where
  scratchSize := h.scratchSize
  factor := h.factor
  code := h.code
  code_spec := h.choose_spec.choose_spec.choose_spec

/-- Strengthen the entry domain or enlarge local work without reselecting any witness data. -/
def Witness.consequence {safe' : ℕ → δ → Memory.State → Prop}
    {work' : δ → Memory.State → ℕ} (h : Witness B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → safe w d s)
    (hwork : ∀ d s, work d s ≤ work' d s) : Witness B p input output safe' work' where
  scratchSize := h.scratchSize
  factor := h.factor
  code := h.code
  code_spec := Spec.consequence h.code_spec hsafe hwork

/-- The client's own admissible history can discharge a stronger entry domain. The supplied
scratch, factor and emitter remain unchanged. -/
def Witness.consequenceValid {safe' : ℕ → δ → Memory.State → Prop}
    (h : Witness B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s) : Witness B p input output safe' work where
  scratchSize := h.scratchSize
  factor := h.factor
  code := h.code
  code_spec := by
    intro r frontier src tmp hi hd hf hs
    obtain ⟨hnw, hrun⟩ := h.code_spec frontier src tmp hi hd hf hs
    refine ⟨hnw, fun w d x hx hin hsafe' hv => hrun w d x hx hin ?_ hv⟩
    exact hsafe w d _ (fun i => congrFun hin i ▸ hx.1 (src i))
      (wellFormed_memoryState hx) hv hsafe'

/-- Exact source equality changes no witness field or code. -/
def Witness.congr {p' : δ → Memory.Prog α} (h : Witness B p input output safe work)
    (hp : ∀ d, p d = p' d) : Witness B p' input output safe work where
  scratchSize := h.scratchSize
  factor := h.factor
  code := h.code
  code_spec := funext hp ▸ h.code_spec

/-- Rewire already live input words by a fixed index map, retaining the supplied resources.
The pointwise encoding equality charges no new host-side argument computation. -/
def Witness.reindex {ε : Type} {m : ℕ} (h : Witness B p input output safe work)
    (f : ε → δ) (env : ε ↪ (Fin m → ℕ)) (ix : Fin k → Fin m)
    (hw : ∀ e i, input (f e) i = env e (ix i)) :
    Witness B (fun e => p (f e)) env output
      (fun w e s => safe w (f e) s) (fun e s => work (f e) s) where
  scratchSize := h.scratchSize
  factor := h.factor
  code := fun frontier src tmp => h.code frontier (src ∘ ix) tmp
  code_spec := Spec.reindex h.code_spec f env ix hw

end Cslib.WordRAM.Realization.Realizes

namespace Cslib.WordRAM.Realization.RealizesBounded

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {k l : ℕ}
  {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

/-- A specified frontier-bounded realization, retaining its resource parameters and emitter. -/
structure Witness (B : Basis) (p : δ → Memory.Prog α) (input : δ ↪ (Fin k → ℕ))
    (output : α ↪ (Fin l → ℕ)) (safe : ℕ → δ → Memory.State → Prop)
    (work : δ → Memory.State → ℕ) where
  /-- Auxiliary registers, excluding results and the reserved extra slot. -/
  scratchSize : ℕ
  /-- Exchange factor for memory charges plus local work. -/
  factor : ℕ
  /-- The emitter, fixed before all runtime values and register placements. -/
  code : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
    (Fin (l + scratchSize + 1) → Fin r) → Code B r
  /-- The frontier-bounded execution, whole-memory/frontier and register-frame contract. -/
  code_spec : Realizes.SpecBounded B p input output safe work scratchSize factor code

/-- Forget resource and emitter selection to `RealizesBounded`. -/
theorem Witness.toRealizesBounded (h : Witness B p input output safe work) :
    RealizesBounded B p input output safe work :=
  ⟨h.scratchSize, h.factor, h.code, h.code_spec⟩

/-- Erase the frontier bound on a retained witness. -/
def Witness.toWitness (h : Witness B p input output safe work) :
    Realizes.Witness B p input output safe work where
  scratchSize := h.scratchSize
  factor := h.factor
  code := h.code
  code_spec := Realizes.SpecBounded.toSpec h.code_spec

/-- Select a witness from an existential `RealizesBounded` proof. -/
noncomputable def Witness.ofRealizesBounded (h : RealizesBounded B p input output safe work) :
    Witness B p input output safe work where
  scratchSize := h.choose
  factor := h.choose_spec.choose
  code := h.choose_spec.choose_spec.choose
  code_spec := h.choose_spec.choose_spec.choose_spec

end Cslib.WordRAM.Realization.RealizesBounded
