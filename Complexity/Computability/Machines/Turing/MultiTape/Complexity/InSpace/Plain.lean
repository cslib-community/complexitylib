/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration

/-!
# Space bounds on plain machines

`Turing.MultiTapeTM.ComputableInSpace` tracks work space (with encoded output charged to the
bound) while leaving running time existentially quantified. This file provides its direct plain
combinator calculus — weakening, encoding transport, composition, pairs, concatenation,
conditionals, finite lookup, binary-counted iteration and list folds — built directly from
`Turing.MultiTapeTM.ComputableInO` without routing through tidy computability.

It also records the equivalence with `Turing.MultiTapeTM.ComputableTidilyInSpace` via
`Turing.MultiTapeTM.ComputableInSpace.tidy` and `Turing.MultiTapeTM.ComputableInSpace.of_tidy`.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.of_inO`, `.exists_inO`: conversion with `ComputableInO`
  retaining the realizing machine.
* `Turing.MultiTapeTM.ComputableInSpace.comp`, `.prod`, `.append`, `.ite`: plain closure rules.
* `Turing.MultiTapeTM.ComputableInSpace.iterate`, `.foldl`, `.foldlWith`: plain space-bounded
  loops.
* `Turing.MultiTapeTM.computableInSpace_iff_computableTidilyInSpace`: equivalence with the tidy
  counterpart.
-/

@[expose] public section

namespace Turing.MultiTapeTM

section Bridge

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {S : α → ℕ}

/-- A function computable within space `O(S)` is tidily computable within it. -/
theorem ComputableInSpace.tidy (h : ComputableInSpace f encIn encOut S) :
    ComputableTidilyInSpace f encIn encOut S := by
  obtain ⟨t, c, hc, hl⟩ := h
  obtain ⟨d, hd, hdl⟩ := hc.computableTidilyInO hl
  refine ⟨t, d * (c + 1), hd.mono (fun a => ?_) (fun a => ?_), fun a => (hdl a).trans ?_⟩
  · nlinarith [Nat.zero_le (d * c * t a)]
  all_goals nlinarith

/-- A function tidily computable within space `O(S)` is computable within it, by the same
machine. -/
theorem ComputableInSpace.of_tidy (h : ComputableTidilyInSpace f encIn encOut S) :
    ComputableInSpace f encIn encOut S :=
  let ⟨_, c, hc, hl⟩ := h
  ⟨_, c, hc.computableInTimeAndSpace, hl⟩

/-- `Turing.MultiTapeTM.ComputableInSpace.of_tidy` for dot notation on a tidy hypothesis. -/
theorem ComputableTidilyInSpace.computableInSpace (h : ComputableTidilyInSpace f encIn encOut S) :
    ComputableInSpace f encIn encOut S :=
  .of_tidy h

/-- **Plain and tidy computability within a space bound agree.** -/
theorem computableInSpace_iff_computableTidilyInSpace :
    ComputableInSpace f encIn encOut S ↔ ComputableTidilyInSpace f encIn encOut S :=
  ⟨ComputableInSpace.tidy, ComputableInSpace.of_tidy⟩

end Bridge

namespace ComputableInSpace

section Combinators

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {encD : δ ↪ List Bool} {S S₁ S₂ : α → ℕ}

/-- Forget the explicit time bound of a `ComputableInO` certificate, retaining its machine. -/
theorem of_inO {α β : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {S : α → ℕ}
    {f : α → β} {T : α → ℕ} (h : ComputableInO f encIn encB T S) :
    ComputableInSpace f encIn encB S :=
  let ⟨c, hc, hl⟩ := h
  ⟨fun a => c * (T a + 1), c, hc, hl⟩

/-- Recover an existentially quantified `ComputableInO` certificate from `ComputableInSpace`,
retaining the same realizing machine. -/
theorem exists_inO {α β : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {S : α → ℕ}
    {f : α → β} (h : ComputableInSpace f encIn encB S) :
    ∃ T, ComputableInO f encIn encB T S := by
  obtain ⟨t, c, hc, hl⟩ := h
  refine ⟨t, max c 1, hc.mono (fun a => ?_) (fun a => ?_), fun a => (hl a).trans ?_⟩
  · have : 1 ≤ max c 1 := le_max_right c 1
    nlinarith
  · exact Nat.mul_le_mul_right _ (le_max_left c 1)
  · exact Nat.mul_le_mul_right _ (le_max_left c 1)

theorem weaken {α β : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {S S₁ : α → ℕ}
    {f : α → β} (h : ComputableInSpace f encIn encB S) (hS : S ≼ S₁) :
    ComputableInSpace f encIn encB S₁ :=
  let ⟨_, hT⟩ := h.exists_inO
  of_inO (hT.weaken (.refl _) hS)

theorem mono_le {α β : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {S S₁ : α → ℕ}
    {f : α → β} (h : ComputableInSpace f encIn encB S) (hS : ∀ a, S a ≤ S₁ a) :
    ComputableInSpace f encIn encB S₁ :=
  h.weaken (.of_le hS)

theorem length_le {α β : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {S : α → ℕ}
    {f : α → β} (h : ComputableInSpace f encIn encB S) :
    (fun a => (encB (f a)).length) ≼ S :=
  let ⟨_, c, _, hl⟩ := h
  ⟨c, hl⟩

theorem of_enc_eq {α β γ : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {S : α → ℕ} {f : α → β} {g : α → γ}
    (h : ComputableInSpace f encIn encB S) (he : ∀ a, encC (g a) = encB (f a)) :
    ComputableInSpace g encIn encC S :=
  let ⟨_, hT⟩ := h.exists_inO
  of_inO (hT.of_enc_eq he)

theorem of_encIn_eq {α α' β : Type*} {encIn : α ↪ List Bool} {encIn' : α' ↪ List Bool}
    {encB : β ↪ List Bool} {S : α → ℕ} {f : α → β} (e : α' → α)
    (h : ComputableInSpace f encIn encB S) (he : ∀ a, encIn' a = encIn (e a)) :
    ComputableInSpace (fun a => f (e a)) encIn' encB fun a => S (e a) :=
  let ⟨_, hT⟩ := h.exists_inO
  of_inO (hT.of_encIn_eq e fun a => (he a).symm)

theorem comp {α β γ : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {S₁ : α → ℕ} {f : α → β} {g : β → γ} {S₂ : β → ℕ}
    (hg : ComputableInSpace g encB encC S₂) (hf : ComputableInSpace f encIn encB S₁) :
    ComputableInSpace (fun a => g (f a)) encIn encC fun a => S₁ a + S₂ (f a) :=
  let ⟨_, hg⟩ := hg.exists_inO
  let ⟨_, hf⟩ := hf.exists_inO
  of_inO (hg.comp hf)

theorem prod {f : α → β} {g : α → γ} (hf : ComputableInSpace f encIn encB S₁)
    (hg : ComputableInSpace g encIn encC S₂) :
    ComputableInSpace (fun a => (f a, g a)) encIn (encPair encB encC)
      fun a => S₁ a + S₂ a :=
  let ⟨_, hf⟩ := hf.exists_inO
  let ⟨_, hg⟩ := hg.exists_inO
  of_inO (hf.prod hg)

theorem append {α β γ δ : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {encD : δ ↪ List Bool} {S₁ S₂ : α → ℕ}
    {f₁ : α → β} {f₂ : α → γ} {g : α → δ}
    (h₁ : ComputableInSpace f₁ encIn encB S₁) (h₂ : ComputableInSpace f₂ encIn encC S₂)
    (hg : ∀ x, encD (g x) = encB (f₁ x) ++ encC (f₂ x)) :
    ComputableInSpace g encIn encD fun x => S₁ x + S₂ x :=
  let ⟨_, h₁⟩ := h₁.exists_inO
  let ⟨_, h₂⟩ := h₂.exists_inO
  of_inO (h₁.append h₂ hg)

theorem ite {α β : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} {S₁ S₂ : α → ℕ}
    {c : α → Bool} {f g : α → β} {Sc : α → ℕ}
    (hc : ComputableInSpace c encIn encBool Sc) (hf : ComputableInSpace f encIn encB S₁)
    (hg : ComputableInSpace g encIn encB S₂) :
    ComputableInSpace (fun a => if c a then f a else g a) encIn encB
      fun a => Sc a + if c a then S₁ a else S₂ a :=
  let ⟨_, hc⟩ := hc.exists_inO
  let ⟨_, hf⟩ := hf.exists_inO
  let ⟨_, hg⟩ := hg.exists_inO
  of_inO (hc.ite hf hg)

theorem const {α β : Type*} {encIn : α ↪ List Bool} {encB : β ↪ List Bool} (b : β) :
    ComputableInSpace (fun _ : α => b) encIn encB fun a => (encIn a).length :=
  of_inO (ComputableInO.const b)

theorem fst (enc₁ : β ↪ List Bool) (enc₂ : γ ↪ List Bool) :
    ComputableInSpace Prod.fst (encPair enc₁ enc₂) enc₁
      fun p => (encPair enc₁ enc₂ p).length :=
  of_inO (ComputableInO.fst enc₁ enc₂)

theorem snd (enc₁ : β ↪ List Bool) (enc₂ : γ ↪ List Bool) :
    ComputableInSpace Prod.snd (encPair enc₁ enc₂) enc₂
      fun p => (encPair enc₁ enc₂ p).length :=
  of_inO (ComputableInO.snd enc₁ enc₂)

theorem fst' {f : α → β × γ} (h : ComputableInSpace f encIn (encPair encB encC) S) :
    ComputableInSpace (fun a => (f a).1) encIn encB S :=
  let ⟨_, h⟩ := h.exists_inO
  of_inO (ComputableInO.fst' h)

theorem snd' {f : α → β × γ} (h : ComputableInSpace f encIn (encPair encB encC) S) :
    ComputableInSpace (fun a => (f a).2) encIn encC S :=
  let ⟨_, h⟩ := h.exists_inO
  of_inO (ComputableInO.snd' h)

theorem of_finite {α β : Type*} [Finite α] {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    (f : α → β) :
    ComputableInSpace f encIn encB fun a => (encIn a).length :=
  of_inO (ComputableInDegree.of_finite f).inO_one

/-- **Iterating a step a computed number of times**, within the space of the counter, of the
initial state, of a round and of the states. -/
theorem iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β} {Sn Si Q B : α → ℕ}
    {Ss : β → ℕ} (hn : ComputableInSpace n encIn encNat Sn)
    (hinit : ComputableInSpace init encIn encB Si)
    (hstep : ComputableInSpace step encB encB Ss)
    (hspace : ∀ x, ∀ k ≤ n x, Ss (step^[k] (init x)) ≤ Q x)
    (hstate : ∀ x, ∀ k ≤ n x, (encB (step^[k] (init x))).length ≤ B x) :
    ComputableInSpace (fun x => step^[n x] (init x)) encIn encB
      fun x => Sn x + Si x + Q x + B x + (encNat (n x)).length := by
  obtain ⟨_, hn⟩ := hn.exists_inO
  obtain ⟨_, hinit⟩ := hinit.exists_inO
  obtain ⟨Ts, hstep⟩ := hstep.exists_inO
  exact of_inO (ComputableInO.iterate hn hinit hstep
    (R := fun x => listMax (fun k => Ts (step^[k] (init x))) (List.range (n x + 1)))
    (fun x k hk => le_listMax (f := fun k => Ts (step^[k] (init x)))
      (List.mem_range.mpr (Nat.lt_succ_of_le hk))) hspace hstate)

/-- **Left folds**, within the space of the list, of the initial state, of a round and of the
states. -/
theorem foldl {encA : δ ↪ List Bool} {encL : List δ ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {list : α → List δ} {init : α → β} {step : β → δ → β}
    {Sl Si Q B : α → ℕ} {Ss : β × δ → ℕ}
    (hlist : ComputableInSpace list encIn encL Sl)
    (hinit : ComputableInSpace init encIn encB Si)
    (hstep : ComputableInSpace (fun p : β × δ => step p.1 p.2) (encPair encB encA) encB Ss)
    (hspace : ∀ x i (hi : i < (list x).length),
      Ss (((list x).take i).foldl step (init x), (list x)[i]) ≤ Q x)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableInSpace (fun x => (list x).foldl step (init x)) encIn encB
      fun x => Sl x + Si x + Q x + B x + (encL (list x)).length := by
  obtain ⟨_, hlist⟩ := hlist.exists_inO
  obtain ⟨_, hinit⟩ := hinit.exists_inO
  obtain ⟨Ts, hstep⟩ := hstep.exists_inO
  exact of_inO (ComputableInO.foldl hlist hinit hstep
    (R := fun x => listMax (fun i => ((list x)[i]?).elim 0 fun a =>
      Ts (((list x).take i).foldl step (init x), a)) (List.range (list x).length))
    (fun x i hi => by
      have := le_listMax (f := fun i => ((list x)[i]?).elim 0 fun a =>
        Ts (((list x).take i).foldl step (init x), a)) (List.mem_range.mpr hi)
      simpa [List.getElem?_eq_getElem hi] using this) hspace hstate)

/-- **Left folds with a parameter**, within the space of the parameter, the list, the initial
state, a round and the states. -/
theorem foldlWith {π : Type} {encP : π ↪ List Bool} {encA : δ ↪ List Bool}
    {encL : List δ ↪ List Bool} [ListEncoding encA encL] [SizedListEncoding encA encL]
    {par : α → π} {list : α → List δ} {init : α → β} {step : π → β → δ → β}
    {Sp Sl Si Q B : α → ℕ} {Ss : (π × β) × δ → ℕ}
    (hpar : ComputableInSpace par encIn encP Sp)
    (hlist : ComputableInSpace list encIn encL Sl)
    (hinit : ComputableInSpace init encIn encB Si)
    (hstep : ComputableInSpace (fun p : (π × β) × δ => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB Ss)
    (hspace : ∀ x i (hi : i < (list x).length),
      Ss ((par x, ((list x).take i).foldl (step (par x)) (init x)), (list x)[i]) ≤ Q x)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableInSpace (fun x => (list x).foldl (step (par x)) (init x)) encIn encB
      fun x => Sp x + Sl x + Si x + Q x + B x + (encP (par x)).length + (encL (list x)).length := by
  obtain ⟨_, hpar⟩ := hpar.exists_inO
  obtain ⟨_, hlist⟩ := hlist.exists_inO
  obtain ⟨_, hinit⟩ := hinit.exists_inO
  obtain ⟨Ts, hstep⟩ := hstep.exists_inO
  exact of_inO (ComputableInO.foldlWith hpar hlist hinit hstep
    (R := fun x => listMax (fun i => ((list x)[i]?).elim 0 fun a =>
      Ts ((par x, ((list x).take i).foldl (step (par x)) (init x)), a))
      (List.range (list x).length))
    (fun x i hi => by
      have := le_listMax (f := fun i => ((list x)[i]?).elim 0 fun a =>
        Ts ((par x, ((list x).take i).foldl (step (par x)) (init x)), a))
        (List.mem_range.mpr hi)
      simpa [List.getElem?_eq_getElem hi] using this) hspace hstate)

end Combinators

end ComputableInSpace

end Turing.MultiTapeTM
