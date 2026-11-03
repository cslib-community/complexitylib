/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
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

* `Data.extend_regs_of_disjoint`: read back an untouched register bank.
* `ExecWithin.call`: inline a fixed-code routine with additive instruction accounting.

These composition lemmas are original and use the existing register-renaming semantics.
-/

public section

namespace Cslib.WordRAM

/-- Writing back one register bank leaves a disjoint bank unchanged. -/
theorem Data.extend_regs_of_disjoint {r s t : ℕ} {f : Fin r → Fin t} {g : Fin s → Fin t}
    (hfg : ∀ i j, f i ≠ g j) (a : Data r) (x : Data t) (j : Fin s) :
    (a.extend f x).regs (g j) = x.regs (g j) := by
  apply Function.extend_apply'
  rintro ⟨i, hi⟩
  exact hfg i j hi

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
  obtain ⟨b, hb, hQ⟩ := hcallee
  have hQ' : Q ((b.extend f a).comap f) := by
    rw [Data.comap_extend hf]
    exact hQ
  obtain ⟨y, hy, hR⟩ := hcont (b.extend f a) hQ' (fun i hi =>
    Function.extend_apply' _ _ _ (by rintro ⟨j, hj⟩; exact hi j hj))
  exact ⟨y, (hprep.seq ((hb.rename hf).seq hy)).mono (by omega), hR⟩

end Cslib.WordRAM
