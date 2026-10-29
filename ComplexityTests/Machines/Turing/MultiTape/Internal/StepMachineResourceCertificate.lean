/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StepMachineComp

/-! # A direct resource-certified streaming emitter

A fixed finite-state machine copies unbounded runtime words in constant workspace. Its whole-run
contract is uncharged, and the charged analogue is refuted explicitly.
-/

@[expose] public section
open Turing Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.StepMachine.Tidy] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus or old bundle: {name}"

namespace ComplexityTests.Internal.StepMachineResourceCertificate

/-- Copy the input in one rightward pass and stop on its final blank. -/
def emitter : StepMachine Bool Bool Bool where
  init := false
  halt := id
  step _ a := match a with
    | none => (true, 0, [])
    | some b => (false, 1, [b])

-- This helper is used only at the fixed Bool and Bool×Option Bool domains of this machine.
-- It does not quantify an unencoded runtime width or a family of finite lookup machines.
private theorem finiteCertificate {α β : Type*} [Finite α] {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} (f : α → β) :
    ComputableInO f encIn encOut (fun _ => 1) (fun _ => 1) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encOut) f
  refine ComputableInO.of_bounds hc c (fun _ => by dsimp; omega)
    (fun _ => by simp) (fun a => ?_)
  have hl := hc.length_le a
  dsimp at hl ⊢
  omega

theorem certificate : emitter.ResourceCertificate encBool (fun _ => 1) (fun _ => 1) where
  computable_halt := finiteCertificate emitter.halt
  computable_step := finiteCertificate (fun p : Bool × Option Bool => emitter.step p.1 p.2)

theorem prefix_run (word : List Bool) (i : ℕ) (hi : i ≤ word.length) :
    (emitter.run word i).state = false ∧ (emitter.run word i).pos.val = i + 1 ∧
      (emitter.run word i).out = word.take i := by
  induction i with
  | zero => simp [StepMachine.run, StepMachine.initCfg, emitter]
  | succ i ih =>
    obtain ⟨hs, hp, ho⟩ := ih (by omega)
    have hi' : i < word.length := by omega
    have hsym : inputSymbolAt word (emitter.run word i).pos = some word[i] := by
      simp [inputSymbolAt, hp, List.getElem?_eq_getElem hi']
    rw [emitter.run_succ_of_not_halt (by simpa [emitter] using hs)]
    simp only [StepMachine.stepAt]
    rw [hsym]
    change false = false ∧
      (moveInputPos (emitter.run word i).pos (1 : SignType)).val = i + 1 + 1 ∧
      (emitter.run word i).out ++ [word[i]] = word.take (i + 1)
    simp only [val_moveInputPos_pos, hp, ho]
    refine ⟨True.intro, by omega, ?_⟩
    exact (List.take_succ_eq_append_getElem hi').symm

theorem finish (word : List Bool) :
    (emitter.run word (word.length + 1)).state = true ∧
      (emitter.run word (word.length + 1)).out = word := by
  obtain ⟨hs, hp, ho⟩ := prefix_run word word.length le_rfl
  have hsym : inputSymbolAt word (emitter.run word word.length).pos = none := by
    simp [inputSymbolAt, hp]
  rw [emitter.run_succ_of_not_halt (by simpa [emitter] using hs)]
  simp only [StepMachine.stepAt]
  rw [hsym]
  change true = true ∧ (emitter.run word word.length).out ++ [] = word
  simp [ho]

theorem halts (word : List Bool) : emitter.HaltsAt word (word.length + 1) := by
  refine ⟨(finish word).1, fun i hi => ?_⟩
  simpa [emitter] using (prefix_run word i (by omega)).1

-- Whole-run uncharged BigO contract, refutation of the charged O analogue, zero-round halted
-- initializer path, and full composition telescope.
example {σf σg : Type} {f : StepMachine σf Bool Bool} {g : StepMachine σg Bool Bool}
    {encF : σf ↪ List Bool} {encG : σg ↪ List Bool}
    {Tf Sf : σf → ℕ} {Tg Sg : σg → ℕ}
    (hf : f.ResourceCertificate encF Tf Sf) (hg : g.ResourceCertificate encG Tg Sg) :
    ComputableInBigO (id : List Bool → List Bool) encBits encBits List.length (fun _ => 1) ∧
    (¬ ComputableInO (id : List Bool → List Bool) encBits encBits List.length (fun _ => 1)) ∧
    (∃ t, ComputableInBigO (fun _ : List Bool => ([] : List Bool)) encBits encBits t (fun _ => 1)) ∧
    (g.comp f).ResourceCertificate (StepMachine.encCompState encF encG)
      (StepMachine.compTime encF encG Tf Sf Tg) (StepMachine.compSpace encF encG Sf Sg) := by
  refine ⟨?_, ?_, ?_, hf.comp hg⟩
  · have h := certificate.computableInBigO (encIn := encBits) (encOut := encBits)
      (id : List Bool → List Bool) (fun w => w.length + 1) halts
      (fun w => (finish w).2.symm)
      (tMax := fun _ => 1) (sMax := fun _ => 1) (by intros; exact ⟨le_rfl, le_rfl⟩)
    exact h.weaken (.of_le_linear 4 6 (by intro w; simp only [encBits_apply]; omega)) (.refl _)
  · rintro ⟨c, _, hlen⟩
    have h := hlen (List.replicate (2 * c + 1) false)
    simp only [id_eq, encBits_apply, List.length_replicate, Nat.one_add] at h
    omega
  · refine ⟨_, certificate.computableInBigO_of_init (encIn := encBits) (encOut := encBits)
      (ComputableInO.constZero true) (fun _ => []) (fun _ => 0)
      (tMax := fun _ => 1) (sMax := fun _ => 1) ?_ ?_ ?_⟩
    · intro w
      simp [StepMachine.HaltsAt, StepMachine.run, StepMachine.initCfg, StepMachine.withInit,
        emitter]
    · intro w
      rfl
    · intros
      exact ⟨le_rfl, le_rfl⟩

end ComplexityTests.Internal.StepMachineResourceCertificate
