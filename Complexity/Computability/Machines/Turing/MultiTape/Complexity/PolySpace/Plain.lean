/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial space on plain machines

`Turing.MultiTapeTM.ComputableInPolySpace`, computability within polynomial space by any machine,
has direct plain closure rules — inclusion of polynomial time, identity, composition, pairing,
conditionals and binary-counted iteration — proved directly via
`Turing.MultiTapeTM.ComputableInSpace` without routing through tidy computability.

The plain predicate and its closure rules are registered with `fun_prop`. It also agrees with its
tidy counterpart `Turing.MultiTapeTM.ComputableTidilyInPolySpace` via
`Turing.MultiTapeTM.ComputableInPolySpace.tidy` and
`Turing.MultiTapeTM.ComputableInPolySpace.of_tidy`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolySpace.of_polyTime`: plain polynomial time is within
  polynomial space.
* `Turing.MultiTapeTM.ComputableInPolySpace.comp`, `.prod`, `.ite`, `.congr`: closure properties.
* `Turing.MultiTapeTM.ComputableInPolySpace.iterate`: iteration within polynomial space.
* `Turing.MultiTapeTM.ComputableInPolyTime.increment`: the binary counter in polynomial time.
* `Turing.MultiTapeTM.computableInPolySpace_iff_computableTidilyInPolySpace`: equivalence with the
  tidy counterpart.
-/

@[expose] public section

namespace Turing.MultiTapeTM

attribute [fun_prop] ComputableInPolySpace

variable {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function computable within polynomial space is tidily computable within polynomial space. -/
theorem ComputableInPolySpace.tidy (h : ComputableInPolySpace f encIn encOut) :
    ComputableTidilyInPolySpace f encIn encOut :=
  let ⟨_, _, hs, hc, hl⟩ := h
  ⟨_, _, .of_polynomiallyBounded _ hs, hc.computableTidilyInO hl⟩

/-- A function tidily computable within polynomial space is computable within polynomial space, by
the same machine. -/
theorem ComputableInPolySpace.of_tidy (h : ComputableTidilyInPolySpace f encIn encOut) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨T, S, ⟨b, hb, hS⟩, c, hc, hl⟩ := h
  have hcS (a : α) : c * (S a + 1) ≤ c * (b (encIn a).length + 1) :=
    Nat.mul_le_mul_left c (Nat.add_le_add_right (hS a) 1)
  exact ⟨_, fun n => c * (b n + 1), by fun_prop,
    hc.computableInTimeAndSpace.mono (fun _ => le_rfl) hcS, fun a => (hl a).trans (hcS a)⟩

/-- `Turing.MultiTapeTM.ComputableInPolySpace.of_tidy` for dot notation on a tidy hypothesis and
the transition used by `fun_prop` to prove plain goals from tidy certificates. -/
@[fun_prop]
theorem ComputableTidilyInPolySpace.computableInPolySpace
    (h : ComputableTidilyInPolySpace f encIn encOut) : ComputableInPolySpace f encIn encOut :=
  .of_tidy h

/-- **Plain and tidy computability within polynomial space agree.** -/
theorem computableInPolySpace_iff_computableTidilyInPolySpace :
    ComputableInPolySpace f encIn encOut ↔ ComputableTidilyInPolySpace f encIn encOut :=
  ⟨ComputableInPolySpace.tidy, ComputableInPolySpace.of_tidy⟩

namespace ComputableInPolySpace

variable {γ δ : Type} {encMid : β ↪ List Bool} {encD : δ ↪ List Bool}

/-- Build `ComputableInPolySpace` from a polynomially bounded `ComputableInSpace` certificate,
retaining the same realizing machine. -/
theorem of_inSpace {S : α → ℕ} (hS : PolyBounded (fun a => (encIn a).length) S)
    (h : ComputableInSpace f encIn encOut S) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨b, hb, hSb⟩ := hS
  obtain ⟨t, c, hc, hl⟩ := h
  have hcS (a : α) : c * (S a + 1) ≤ c * (b (encIn a).length + 1) :=
    Nat.mul_le_mul_left c (Nat.add_le_add_right (hSb a) 1)
  exact ⟨t, fun n => c * (b n + 1), by fun_prop,
    hc.mono (fun _ => le_rfl) hcS, fun a => (hl a).trans (hcS a)⟩

/-- Unpack `ComputableInPolySpace` into a polynomially bounded `ComputableInSpace` certificate,
retaining the same realizing machine. -/
theorem exists_inSpace (h : ComputableInPolySpace f encIn encOut) :
    ∃ S, PolyBounded (fun a => (encIn a).length) S ∧ ComputableInSpace f encIn encOut S := by
  obtain ⟨t, s, hs, hc, hl⟩ := h
  refine ⟨fun a => s (encIn a).length, .of_polynomiallyBounded _ hs, t, 1,
    hc.mono (fun _ => le_rfl) (fun a => by dsimp only; omega),
    fun a => (hl a).trans (by dsimp only; omega)⟩

/-- Encoded outputs of a polynomial-space function have polynomially bounded length. -/
theorem polyBounded_length (h : ComputableInPolySpace f encIn encOut) :
    PolyBounded (fun a => (encIn a).length) fun a => (encOut (f a)).length := by
  obtain ⟨_, s, hs, _, hl⟩ := h
  exact (PolyBounded.of_polynomiallyBounded _ hs).mono hl

/-! ### Closure and automation -/

/-- Polynomial time is within polynomial space. -/
@[fun_prop]
theorem of_polyTime (h : ComputableInPolyTime f encIn encOut) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨t, s, ht, hs, hc⟩ := h
  exact ⟨fun a => t (encIn a).length, fun n => t n + s n, by fun_prop,
    hc.mono (fun _ => le_rfl) (fun _ => Nat.le_add_left _ _),
    fun a => (hc.length_le a).trans (Nat.le_add_right _ _)⟩

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
