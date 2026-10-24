/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Foundations.Data.BitString.Counter
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Tidy computability within polynomial space

`Turing.MultiTapeTM.ComputableTidilyInPolySpace f encIn encOut`: `f` is tidily computable
(`Turing.MultiTapeTM.ComputableTidilyInO`) within some time and within space polynomially bounded in
the length of the encoded input. Unlike `Turing.MultiTapeTM.ComputableTidilyInPolyTime`, no bound on
the time is imposed, so the notion is closed under iterating a step an exponential number of times,
counted in binary, as long as the states stay of polynomial size
(`Turing.MultiTapeTM.ComputableTidilyInPolySpace.iterate`). It is also closed under composition,
pairing and case distinction, and contains polynomial time; these closure properties are registered
with `fun_prop`. A Boolean function computable within polynomial space decides a problem in `PSPACE`
(`Cslib.Complexity.mem_PSPACE_iff_computableInPolySpace`).

Exhaustive searches within polynomial space enumerate their candidates with the binary counter
`Cslib.BitString.increment`, which is computable in linear time
(`Turing.MultiTapeTM.ComputableTidilyInDegree.increment`).

## Main definitions

* `Turing.MultiTapeTM.ComputableTidilyInPolySpace`: computability within polynomial space.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolySpace.of_polyTime`: polynomial time is within
  polynomial space.
* `Turing.MultiTapeTM.ComputableTidilyInPolySpace.comp`, `.prod`, `.ite`: closure properties.
* `Turing.MultiTapeTM.ComputableTidilyInPolySpace.iterate`: iteration within polynomial space.
* `Turing.MultiTapeTM.ComputableTidilyInDegree.increment`: the binary counter in linear time.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- `f` is tidily computable within some time and within space polynomially bounded in the length
of the encoded input. -/
def ComputableTidilyInPolySpace {α β : Type} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ T S, PolyBounded (fun a => (encIn a).length) S ∧ ComputableTidilyInO f encIn encOut T S

namespace ComputableTidilyInPolySpace

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {encD : δ ↪ List Bool}

/-- **Polynomial time is within polynomial space.** -/
theorem of_polyTime {f : α → β} (h : ComputableTidilyInPolyTime f encIn encMid) :
    ComputableTidilyInPolySpace f encIn encMid := by
  obtain ⟨d, _, h⟩ := h.exists_degree
  exact ⟨_, _, PolyBounded.of_forall_le (u := fun a => ((encIn a).length + 1) ^ d) 1 d
    fun a => by simp, h.inO⟩

/-- The encoded values have polynomial length. -/
theorem polyBounded_length {f : α → β} (h : ComputableTidilyInPolySpace f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) fun a => (encMid (f a)).length := by
  obtain ⟨T, S, hS, h⟩ := h
  obtain ⟨c, hc⟩ := h.length_le
  exact ((PolyBounded.const c).mul (hS.add (.const 1))).mono hc

/-- Composition. -/
theorem comp {f : β → γ} {g : α → β} (hf : ComputableTidilyInPolySpace f encMid encOut)
    (hg : ComputableTidilyInPolySpace g encIn encMid) :
    ComputableTidilyInPolySpace (fun a => f (g a)) encIn encOut := by
  have hlen := hg.polyBounded_length
  obtain ⟨Tf, Sf, hSf, hf'⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg'⟩ := hg
  exact ⟨_, _, hSg.add (hSf.comp hlen), hf'.comp hg'⟩

/-- The identity. -/
theorem id' : ComputableTidilyInPolySpace (fun a : α => a) encIn encIn :=
  of_polyTime ComputableTidilyInPolyTime.id'

/-- Pairing. -/
theorem prod {f : α → β} {g : α → δ} (hf : ComputableTidilyInPolySpace f encIn encMid)
    (hg : ComputableTidilyInPolySpace g encIn encD) :
    ComputableTidilyInPolySpace (fun a => (f a, g a)) encIn (encPair encMid encD) := by
  obtain ⟨Tf, Sf, hSf, hf⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg⟩ := hg
  exact ⟨_, _, hSf.add hSg, hf.prod hg⟩

/-- Case distinction. -/
theorem ite {c : α → Bool} {f g : α → β} (hc : ComputableTidilyInPolySpace c encIn encBool)
    (hf : ComputableTidilyInPolySpace f encIn encMid)
    (hg : ComputableTidilyInPolySpace g encIn encMid) :
    ComputableTidilyInPolySpace (fun a => if c a then f a else g a) encIn encMid := by
  obtain ⟨Tc, Sc, hSc, hc⟩ := hc
  obtain ⟨Tf, Sf, hSf, hf⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg⟩ := hg
  refine ⟨_, _, (hSc.add (hSf.add hSg)).mono fun a => ?_, hc.ite hf hg⟩
  split_ifs <;> lia

/-- Agreement with a function computable within polynomial space. -/
theorem congr {f g : α → β} (h : ComputableTidilyInPolySpace f encIn encMid)
    (hfg : ∀ a, f a = g a) : ComputableTidilyInPolySpace g encIn encMid := by
  rwa [show g = f from funext fun a => (hfg a).symm]

/-- **Iteration within polynomial space**: iterating a step computable within polynomial space a
number of times computed in polynomial time in binary, from a start computable within polynomial
space, is within polynomial space when all the states along the way have polynomial length. -/
theorem iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β}
    (hn : ComputableTidilyInPolyTime n encIn encNat)
    (hinit : ComputableTidilyInPolySpace init encIn encMid)
    (hstep : ComputableTidilyInPolySpace step encMid encMid) {B : α → ℕ}
    (hB : PolyBounded (fun a => (encIn a).length) B)
    (hstate : ∀ a, ∀ k ≤ n a, (encMid (step^[k] (init a))).length ≤ B a) :
    ComputableTidilyInPolySpace (fun a => step^[n a] (init a)) encIn encMid := by
  obtain ⟨dn, _, hn'⟩ := hn.exists_degree
  obtain ⟨Ti, Si, hSi, hinit⟩ := hinit
  obtain ⟨Ts, Ss, hSs, hstep⟩ := hstep
  obtain ⟨cs, ds, hSs⟩ := hSs.exists_le
  have hit := ComputableTidilyInO.iterate hn'.inO hinit hstep
    (R := fun a => (Finset.range (n a + 1)).sup fun k => Ts (step^[k] (init a)))
    (Q := fun a => cs * (B a + 1) ^ ds) (B := B)
    (fun a k hk => Finset.le_sup (f := fun k => Ts (step^[k] (init a)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    (fun a k hk => (hSs _).trans (Nat.mul_le_mul_left cs
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a k hk) 1) ds)))
    hstate
  refine ⟨_, _, ?_, hit⟩
  have hQ : PolyBounded (fun a => (encIn a).length) fun a => cs * (B a + 1) ^ ds :=
    PolyBounded.comp (size' := id) (v := fun m => cs * (m + 1) ^ ds)
      (PolyBounded.of_forall_le cs ds fun _ => le_rfl) hB
  exact ((((PolyBounded.of_forall_le (u := fun a => ((encIn a).length + 1) ^ dn) 1 dn
    fun a => by simp).add hSi).add hQ).add hB).add hn.polyBounded_length

/-! ### Automation -/

attribute [fun_prop] ComputableTidilyInPolySpace of_polyTime id' prod ite

/-- Composition, in the form used by `fun_prop`. -/
@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} (hf : ComputableTidilyInPolySpace f encMid encOut)
    (hg : ComputableTidilyInPolySpace g encIn encMid) :
    ComputableTidilyInPolySpace (fun a => f (g a)) encIn encOut :=
  hf.comp hg

end ComputableTidilyInPolySpace

/-! ### The binary counter -/

/-- Increment by a two-state transducer, the state being the carry. -/
private def incrementT : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [b ^^ c])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem incrementT_run_false (w : List Bool) : incrementT.run false w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ false] ++ incrementT.run (false && b) w = b :: w
    rw [Bool.false_and, ih, Bool.xor_false]
    rfl

private theorem incrementT_run (w : List Bool) :
    incrementT.run true w = Cslib.BitString.increment w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ true] ++ incrementT.run (true && b) w = Cslib.BitString.increment (b :: w)
    cases b
    · rw [Bool.true_and, incrementT_run_false]
      rfl
    · rw [Bool.true_and, ih]
      rfl

/-- **The binary counter in linear time.** -/
theorem ComputableTidilyInDegree.increment :
    ComputableTidilyInDegree Cslib.BitString.increment encBits encBits 1 1 :=
  .of_linear (incrementT.computableTidilyInLinearTimeAndSpace fun w => by
    rw [show incrementT.q₀ = true from rfl, incrementT_run]; rfl)

/-- The binary counter in polynomial time. -/
@[fun_prop]
theorem ComputableTidilyInPolyTime.increment :
    ComputableTidilyInPolyTime Cslib.BitString.increment encBits encBits :=
  ComputableTidilyInDegree.increment.computableTidilyInPolyTime

end Turing.MultiTapeTM
