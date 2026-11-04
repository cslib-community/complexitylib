/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Calling fixed code in a register bank

`ExecWithin.call` combines charged argument preparation, a proved routine in an injectively
renamed register bank, and a charged continuation. The continuation receives the routine's entire
postcondition and the unchanged registers outside its bank. The postcondition may describe both
results and memory frames: register renaming leaves memory unchanged, so no separate memory
transport proof is needed.

Unlike bounded-footprint data-structure contracts, this rule does not require every word in the
caller state to fit or specify a finite footprint. It retains exactly the hypotheses of the
supplied execution proof, including routines that tolerate arbitrary unused memory.

## Main results

* `Data.comap_set`, `Data.comap_set_of_forall_ne`: transport register updates through a bank view.
* `Exec.rename_post`, `ExecWithin.rename_post`: retain postconditions and the caller register frame.
* `ExecWithin.call`: inline a fixed-code routine with additive instruction accounting.

These composition lemmas use the existing register-renaming semantics. `Data.comap_set`
was extracted from the priority-queue calling convention by Renfei Zhou.
-/

public section

namespace Cslib.WordRAM

/-- Updating an embedded register updates the corresponding register in the bank view. -/
theorem Data.comap_set {r s : ℕ} {f : Fin r → Fin s} (hf : f.Injective)
    (x : Data s) (i : Fin r) (v : ℕ) :
    (x.set (f i) v).comap f = (x.comap f).set i v :=
  Data.ext (Function.update_comp_eq_of_injective _ hf i v) rfl

/-- A register update outside a bank leaves its entire view unchanged. -/
theorem Data.comap_set_of_forall_ne {r s : ℕ} {f : Fin r → Fin s}
    (x : Data s) (i : Fin s) (v : ℕ) (hi : ∀ j, f j ≠ i) :
    (x.set i v).comap f = x.comap f :=
  Data.ext (Function.update_comp_eq_of_forall_ne _ v hi) rfl

/-- Run a routine in a larger register file, retaining its entire postcondition and the frame
outside its bank. Renaming preserves the exact instruction count. -/
theorem Exec.rename_post {B : Basis} {r s w t : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s} {Q : Data r → Prop}
    (h : ∃ y, Exec w c (x.comap f) y t ∧ Q y) :
    ∃ y, Exec w (c.rename f) x y t ∧ Q (y.comap f) ∧
      ∀ i, (∀ j, f j ≠ i) → y.regs i = x.regs i := by
  obtain ⟨y, hy, hQ⟩ := h
  refine ⟨y.extend f x, hy.rename hf, (Data.comap_extend hf y x).symm ▸ hQ, ?_⟩
  exact fun i hi => Function.extend_apply' _ _ _ (by rintro ⟨j, hj⟩; exact hi j hj)

/-- Bounded-time version of `Exec.rename_post`. -/
theorem ExecWithin.rename_post {B : Basis} {r s w t : ℕ} {f : Fin r → Fin s}
    (hf : f.Injective) {c : Code B r} {x : Data s} {Q : Data r → Prop}
    (h : ∃ y, ExecWithin w c (x.comap f) y t ∧ Q y) :
    ∃ y, ExecWithin w (c.rename f) x y t ∧ Q (y.comap f) ∧
      ∀ i, (∀ j, f j ≠ i) → y.regs i = x.regs i := by
  obtain ⟨y, ⟨n, hn, hy⟩, hQ⟩ := h
  obtain ⟨z, hz, hQ, hframe⟩ := Exec.rename_post hf ⟨y, hy, hQ⟩
  exact ⟨z, hz.within.mono hn, hQ, hframe⟩

/-- Call a routine in an injective register bank and pass its postcondition and register frame to
the continuation. Preparation, routine execution, and continuation are all charged; renaming
itself emits no instruction. Any memory assertion in `Q` refers to the actual returned memory. -/
theorem ExecWithin.call {B : Basis} {r r' w tPrep tCall tCont : ℕ}
    {f : Fin r → Fin r'} (hf : f.Injective)
    {prep cont : Code B r'} {callee : Code B r} {x a : Data r'}
    {Q : Data r → Prop} {R : Data r' → Prop}
    (hprep : ExecWithin w prep x a tPrep)
    (hcallee : ∃ b, ExecWithin w callee (a.comap f) b tCall ∧ Q b)
    (hcont : ∀ b, Q (b.comap f) →
      (∀ i, (∀ j, f j ≠ i) → b.regs i = a.regs i) →
      ∃ y, ExecWithin w cont b y tCont ∧ R y) :
    ∃ y, ExecWithin w (.seq prep (.seq (callee.rename f) cont)) x y
      (tPrep + tCall + tCont) ∧ R y := by
  obtain ⟨b, hb, hQ, hframe⟩ := rename_post hf hcallee
  obtain ⟨y, hy, hR⟩ := hcont b hQ hframe
  exact ⟨y, (hprep.seq (hb.seq hy)).mono (by omega), hR⟩

end Cslib.WordRAM
