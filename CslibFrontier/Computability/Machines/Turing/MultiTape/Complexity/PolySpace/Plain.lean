/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial space on plain machines

`Turing.MultiTapeTM.ComputableInPolySpace`, computability within polynomial space by any machine,
has direct plain closure rules — identity, composition, pairing, conditionals and binary-counted
iteration — proved directly via `Turing.MultiTapeTM.ComputableInSpace` without routing through
tidy computability. The certificates and the inclusion of polynomial time
(`Turing.MultiTapeTM.ComputableInPolySpace.of_polyTime`) are in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Basic`.

The closure rules are registered with `fun_prop`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolySpace.polyBounded_length`: encoded outputs have polynomially
  bounded length.
* `Turing.MultiTapeTM.ComputableInPolySpace.comp`, `.prod`, `.ite`, `.congr`: closure properties.
* `Turing.MultiTapeTM.ComputableInPolySpace.iterate`: iteration within polynomial space.
* `Turing.MultiTapeTM.ComputableInPolyTime.increment`: the binary counter in polynomial time.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

namespace ComputableInPolySpace

variable {γ δ : Type} {encMid : β ↪ List Bool} {encD : δ ↪ List Bool}

/-- Encoded outputs of a polynomial-space function have polynomially bounded length. -/
theorem polyBounded_length (h : ComputableInPolySpace f encIn encOut) :
    PolyBounded (fun a => (encIn a).length) fun a => (encOut (f a)).length := by
  obtain ⟨_, s, hs, _, hl⟩ := h
  exact (PolyBounded.of_polynomiallyBounded _ hs).mono hl

/-! ### Closure and automation -/

/-- The identity. -/
@[fun_prop]
theorem id' : ComputableInPolySpace (fun a : α => a) encIn encIn :=
  of_polyTime ComputableInPolyTime.id'

/-- Composition. -/
theorem comp {f : β → γ} {g : α → β} {encOut : γ ↪ List Bool}
    (hf : ComputableInPolySpace f encMid encOut) (hg : ComputableInPolySpace g encIn encMid) :
    ComputableInPolySpace (fun a => f (g a)) encIn encOut := by
  have hlen := hg.polyBounded_length
  obtain ⟨Sf, hSf, hfS⟩ := hf.exists_inSpace
  obtain ⟨Sg, hSg, hgS⟩ := hg.exists_inSpace
  exact of_inSpace (hSg.add (hSf.comp hlen)) (hfS.comp hgS)

/-- Pairing. -/
@[fun_prop]
theorem prod {g : α → δ} (hf : ComputableInPolySpace f encIn encOut)
    (hg : ComputableInPolySpace g encIn encD) :
    ComputableInPolySpace (fun a => (f a, g a)) encIn (encPair encOut encD) := by
  obtain ⟨Sf, hSf, hfS⟩ := hf.exists_inSpace
  obtain ⟨Sg, hSg, hgS⟩ := hg.exists_inSpace
  exact of_inSpace (hSf.add hSg) (hfS.prod hgS)

/-- Case distinction. -/
@[fun_prop]
theorem ite {c : α → Bool} {g : α → β} (hc : ComputableInPolySpace c encIn encBool)
    (hf : ComputableInPolySpace f encIn encOut) (hg : ComputableInPolySpace g encIn encOut) :
    ComputableInPolySpace (fun a => if c a then f a else g a) encIn encOut := by
  obtain ⟨Sc, hSc, hcS⟩ := hc.exists_inSpace
  obtain ⟨Sf, hSf, hfS⟩ := hf.exists_inSpace
  obtain ⟨Sg, hSg, hgS⟩ := hg.exists_inSpace
  refine of_inSpace ((hSc.add (hSf.add hSg)).mono fun a => ?_) (hcS.ite hfS hgS)
  split_ifs <;> omega

/-- Agreement with a function computable within polynomial space. -/
theorem congr {g : α → β} (h : ComputableInPolySpace f encIn encOut) (hfg : ∀ a, f a = g a) :
    ComputableInPolySpace g encIn encOut := by
  rwa [show g = f from funext fun a => (hfg a).symm]

/-- **Iteration within polynomial space**: iterating a step computable within polynomial space a
number of times computed in polynomial time in binary, from a start computable within polynomial
space, is within polynomial space when all the states along the way have polynomial length. -/
theorem iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β}
    (hn : ComputableInPolyTime n encIn encNat) (hinit : ComputableInPolySpace init encIn encOut)
    (hstep : ComputableInPolySpace step encOut encOut) {B : α → ℕ}
    (hB : PolyBounded (fun a => (encIn a).length) B)
    (hstate : ∀ a, ∀ k ≤ n a, (encOut (step^[k] (init a))).length ≤ B a) :
    ComputableInPolySpace (fun a => step^[n a] (init a)) encIn encOut := by
  have hnPS := of_polyTime hn
  obtain ⟨Sn, hSn, hnS⟩ := hnPS.exists_inSpace
  obtain ⟨Si, hSi, hiS⟩ := hinit.exists_inSpace
  obtain ⟨Ss, hSs, hsS⟩ := hstep.exists_inSpace
  obtain ⟨cs, ds, hSs_le⟩ := hSs.exists_le
  have hQ : PolyBounded (fun a => (encIn a).length) fun a => cs * (B a + 1) ^ ds :=
    PolyBounded.comp (size' := id) (v := fun m => cs * (m + 1) ^ ds)
      (PolyBounded.of_forall_le cs ds fun _ => le_rfl) hB
  exact of_inSpace ((((hSn.add hSi).add hQ).add hB).add hnPS.polyBounded_length)
    (ComputableInSpace.iterate hnS hiS hsS
      (Q := fun a => cs * (B a + 1) ^ ds)
      (fun a k hk => (hSs_le _).trans (Nat.mul_le_mul_left cs
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a k hk) 1) ds)))
      hstate)

/-- Composition, in the form used by `fun_prop`. -/
@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} {encOut : γ ↪ List Bool}
    (hf : ComputableInPolySpace f encMid encOut) (hg : ComputableInPolySpace g encIn encMid) :
    ComputableInPolySpace (fun a => f (g a)) encIn encOut :=
  hf.comp hg

end ComputableInPolySpace

private def incrementTransducer : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [b ^^ c])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem incrementTransducer_run_false (w : List Bool) :
    incrementTransducer.run false w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ false] ++ incrementTransducer.run (false && b) w = b :: w
    rw [Bool.false_and, ih, Bool.xor_false]
    rfl

private theorem incrementTransducer_run (w : List Bool) :
    incrementTransducer.run true w = Cslib.BitString.increment w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ true] ++ incrementTransducer.run (true && b) w =
      Cslib.BitString.increment (b :: w)
    cases b
    · rw [Bool.true_and, incrementTransducer_run_false]
      rfl
    · rw [Bool.true_and, ih]
      rfl

/-- The binary counter in polynomial time. -/
theorem ComputableInPolyTime.increment :
    ComputableInPolyTime Cslib.BitString.increment encBits encBits := by
  refine ⟨fun n => 2 * n + 3, fun _ => 0, by fun_prop, by fun_prop,
    0, _, inferInstance, incrementTransducer.toTM, fun w => ?_⟩
  simpa only [encBits_apply, show incrementTransducer.q₀ = true from rfl,
    incrementTransducer_run] using incrementTransducer.computesInTimeAndSpace_toTM w

end Turing.MultiTapeTM
