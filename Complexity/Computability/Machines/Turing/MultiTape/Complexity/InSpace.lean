/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration

/-!
# Tidy computability within a space bound

`ComputableTidilyInSpace f encIn encOut S` says that `f` is tidily computable within space `O(S)`,
with values of length `O(S)`, in some time. For space-bounded algorithms only the work space
matters, and this calculus tracks it alone: composition, pairs, conditionals and loops keep the
work space explicit and leave the time to be whatever it is. In loops, the time of a round is the
largest over the rounds actually run.

## Main definitions

* `Turing.MultiTapeTM.ComputableTidilyInSpace`: tidy computability within a space bound.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInSpace.comp`, `.prod`, `.ite`: closure properties.
* `Turing.MultiTapeTM.ComputableTidilyInSpace.iterate`, `.foldl`: loops.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- `f` is tidily computable within space `O(S a)` on the input `a`, and its encoded value has
length `O(S a)`, in some time. -/
def ComputableTidilyInSpace {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (S : α → ℕ) : Prop :=
  ∃ T, ComputableTidilyInO f encIn encOut T S

namespace ComputableTidilyInSpace

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {encD : δ ↪ List Bool} {S S₁ S₂ : α → ℕ}

theorem of_inO {f : α → β} {T : α → ℕ} (h : ComputableTidilyInO f encIn encB T S) :
    ComputableTidilyInSpace f encIn encB S :=
  ⟨T, h⟩

theorem weaken {f : α → β} (h : ComputableTidilyInSpace f encIn encB S) (hS : S ≼ S₁) :
    ComputableTidilyInSpace f encIn encB S₁ :=
  let ⟨T, hT⟩ := h
  ⟨T, hT.weaken (.refl _) hS⟩

theorem length_le {f : α → β} (h : ComputableTidilyInSpace f encIn encB S) :
    (fun a => (encB (f a)).length) ≼ S :=
  let ⟨_, hT⟩ := h
  hT.length_le

theorem of_enc_eq {f : α → β} {g : α → γ} (h : ComputableTidilyInSpace f encIn encB S)
    (he : ∀ a, encC (g a) = encB (f a)) : ComputableTidilyInSpace g encIn encC S :=
  let ⟨T, hT⟩ := h
  ⟨T, hT.of_enc_eq he⟩

theorem comp {f : α → β} {g : β → γ} {S₂ : β → ℕ} (hg : ComputableTidilyInSpace g encB encC S₂)
    (hf : ComputableTidilyInSpace f encIn encB S₁) :
    ComputableTidilyInSpace (fun a => g (f a)) encIn encC fun a => S₁ a + S₂ (f a) :=
  let ⟨_, hg⟩ := hg
  let ⟨_, hf⟩ := hf
  ⟨_, hg.comp hf⟩

theorem prod {f : α → β} {g : α → γ} (hf : ComputableTidilyInSpace f encIn encB S₁)
    (hg : ComputableTidilyInSpace g encIn encC S₂) :
    ComputableTidilyInSpace (fun a => (f a, g a)) encIn (encPair encB encC)
      fun a => S₁ a + S₂ a :=
  let ⟨_, hf⟩ := hf
  let ⟨_, hg⟩ := hg
  ⟨_, hf.prod hg⟩

theorem ite {c : α → Bool} {f g : α → β} {Sc : α → ℕ}
    (hc : ComputableTidilyInSpace c encIn encBool Sc) (hf : ComputableTidilyInSpace f encIn encB S₁)
    (hg : ComputableTidilyInSpace g encIn encB S₂) :
    ComputableTidilyInSpace (fun a => if c a then f a else g a) encIn encB
      fun a => Sc a + if c a then S₁ a else S₂ a :=
  let ⟨_, hc⟩ := hc
  let ⟨_, hf⟩ := hf
  let ⟨_, hg⟩ := hg
  ⟨_, hc.ite hf hg⟩

theorem const (b : β) :
    ComputableTidilyInSpace (fun _ : α => b) encIn encB fun a => (encIn a).length :=
  of_inO (ComputableTidilyInO.const b)

theorem fst (enc₁ : β ↪ List Bool) (enc₂ : γ ↪ List Bool) :
    ComputableTidilyInSpace Prod.fst (encPair enc₁ enc₂) enc₁
      fun p => (encPair enc₁ enc₂ p).length :=
  of_inO (ComputableTidilyInO.fst enc₁ enc₂)

theorem snd (enc₁ : β ↪ List Bool) (enc₂ : γ ↪ List Bool) :
    ComputableTidilyInSpace Prod.snd (encPair enc₁ enc₂) enc₂
      fun p => (encPair enc₁ enc₂ p).length :=
  of_inO (ComputableTidilyInO.snd enc₁ enc₂)

theorem fst' {f : α → β × γ} (h : ComputableTidilyInSpace f encIn (encPair encB encC) S) :
    ComputableTidilyInSpace (fun a => (f a).1) encIn encB S :=
  let ⟨_, h⟩ := h
  ⟨_, ComputableTidilyInO.fst' h⟩

theorem snd' {f : α → β × γ} (h : ComputableTidilyInSpace f encIn (encPair encB encC) S) :
    ComputableTidilyInSpace (fun a => (f a).2) encIn encC S :=
  let ⟨_, h⟩ := h
  ⟨_, ComputableTidilyInO.snd' h⟩

theorem of_finite [Finite α] (f : α → β) :
    ComputableTidilyInSpace f encIn encB fun a => (encIn a).length :=
  of_inO (ComputableTidilyInDegree.of_finite f).inO_one

/-- **Iterating a step a computed number of times**, within the space of the counter, of the
initial state, of a round and of the states. -/
theorem iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β} {Sn Si Q B : α → ℕ}
    {Ss : β → ℕ} (hn : ComputableTidilyInSpace n encIn encNat Sn)
    (hinit : ComputableTidilyInSpace init encIn encB Si)
    (hstep : ComputableTidilyInSpace step encB encB Ss)
    (hspace : ∀ x, ∀ k ≤ n x, Ss (step^[k] (init x)) ≤ Q x)
    (hstate : ∀ x, ∀ k ≤ n x, (encB (step^[k] (init x))).length ≤ B x) :
    ComputableTidilyInSpace (fun x => step^[n x] (init x)) encIn encB
      fun x => Sn x + Si x + Q x + B x + (encNat (n x)).length := by
  obtain ⟨_, hn⟩ := hn
  obtain ⟨_, hinit⟩ := hinit
  obtain ⟨Ts, hstep⟩ := hstep
  exact ⟨_, (ComputableInO.iterate hn.computableInO hinit.computableInO hstep.computableInO
    (R := fun x => listMax (fun k => Ts (step^[k] (init x))) (List.range (n x + 1)))
    (fun x k hk => le_listMax (f := fun k => Ts (step^[k] (init x)))
      (List.mem_range.mpr (Nat.lt_succ_of_le hk))) hspace hstate).tidy⟩

/-- **Left folds**, within the space of the list, of the initial state, of a round and of the
states. -/
theorem foldl {encA : δ ↪ List Bool} {encL : List δ ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {list : α → List δ} {init : α → β} {step : β → δ → β}
    {Sl Si Q B : α → ℕ} {Ss : β × δ → ℕ}
    (hlist : ComputableTidilyInSpace list encIn encL Sl)
    (hinit : ComputableTidilyInSpace init encIn encB Si)
    (hstep : ComputableTidilyInSpace (fun p : β × δ => step p.1 p.2) (encPair encB encA) encB Ss)
    (hspace : ∀ x i (hi : i < (list x).length),
      Ss (((list x).take i).foldl step (init x), (list x)[i]) ≤ Q x)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableTidilyInSpace (fun x => (list x).foldl step (init x)) encIn encB
      fun x => Sl x + Si x + Q x + B x + (encL (list x)).length := by
  obtain ⟨_, hlist⟩ := hlist
  obtain ⟨_, hinit⟩ := hinit
  obtain ⟨Ts, hstep⟩ := hstep
  exact ⟨_, (ComputableInO.foldl hlist.computableInO hinit.computableInO hstep.computableInO
    (R := fun x => listMax (fun i => ((list x)[i]?).elim 0 fun a =>
      Ts (((list x).take i).foldl step (init x), a)) (List.range (list x).length))
    (fun x i hi => by
      have := le_listMax (f := fun i => ((list x)[i]?).elim 0 fun a =>
        Ts (((list x).take i).foldl step (init x), a)) (List.mem_range.mpr hi)
      simpa [List.getElem?_eq_getElem hi] using this) hspace hstate).tidy⟩

end ComputableTidilyInSpace

end Turing.MultiTapeTM
