/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite

/-!
# Case analysis on a component, within given bounds

Case analysis on the second component of a pair, when that component is a tagged sum
(`Turing.MultiTapeTM.encSum`) or an option (`Turing.MultiTapeTM.encOption`). Each branch need
only be computable on its own case, and only the branch taken is charged, plus the length of the
encoded input. No default values of the component types are needed: the branches run on the
inputs of their case only.

## Main results

* `Turing.MultiTapeTM.ComputableInO.sumElimSnd`: case analysis on a sum component.
* `Turing.MultiTapeTM.ComputableInO.optionElimSnd`: case analysis on an option component.
-/

public section

namespace Turing.MultiTapeTM.ComputableTidilyInO

variable {π α β ε : Type} {encP : π ↪ List Bool} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encE : ε ↪ List Bool}

/-- A function whose encoded value is obtained from the encoded input by keeping its leading frame
and dropping `k` symbols after it, in linear time. -/
private lemma keepFrame_drop {σ : Type} {encS : σ ↪ List Bool} {h : σ → π × α} (k : ℕ)
    (hh : ∀ s, ∃ u, encS s = frame (encP (h s).1) ++ u ∧ encA (h s).2 = u.drop k) :
    ComputableTidilyInO h encS (encPair encP encA) (fun s => (encS s).length)
      (fun s => (encS s).length) := by
  have hlen : ∀ s, (encP (h s).1).length + (encA (h s).2).length ≤ (encS s).length := fun s => by
    obtain ⟨u, hs, hu⟩ := hh s
    rw [hs, hu, List.length_append, length_frame, List.length_drop]
    omega
  have h₁ : ComputableTidilyInO (fun s => (h s).1) encS (encFramed encP)
      (fun s => (encS s).length) (fun s => (encS s).length) := by
    have hu : ComputableTidilyInO (fun s => (h s).1) encS encP (fun s => (encS s).length)
        (fun s => (encS s).length) :=
      of_linear (.of_unframe fun s => by
        obtain ⟨u, hs, -⟩ := hh s
        rw [hs, unframe_frame_append])
    refine ((of_linear (.of_frame (f := fun x : π => x) (encIn := encP)
      (encOut := encFramed encP) fun _ => rfl)).comp hu).mono 2 (fun s => ?_) (fun s => ?_) <;>
    · have := hlen s
      omega
  -- the word after the frame, then `k` symbols dropped
  have hd : ComputableTidilyInO (fun s => dropFrame (encS s)) encS encBits
      (fun s => (encS s).length) (fun s => (encS s).length) :=
    of_linear (.of_dropFrame fun s => rfl)
  have hdrop : ∀ k : ℕ, ComputableTidilyInO (fun s => (dropFrame (encS s)).drop k) encS encBits
      (fun s => (encS s).length) (fun s => (encS s).length) := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      refine (((of_linear (.of_tail (f := List.tail) (encIn := encBits) (encOut := encBits)
        fun _ => rfl)).comp ih).of_enc_eq (g := fun s => (dropFrame (encS s)).drop (k + 1))
        fun s => by simp [encBits, List.tail_drop]).mono 2 (fun s => ?_) (fun s => ?_) <;>
      · have : ((dropFrame (encS s)).drop k).length ≤ (encS s).length := by
          obtain ⟨u, hs, -⟩ := hh s
          rw [hs, dropFrame_frame_append, List.length_drop, List.length_append]
          omega
        simp only [encBits, Function.Embedding.refl_apply]
        omega
  have h₂ : ComputableTidilyInO (fun s => (h s).2) encS encA (fun s => (encS s).length)
      (fun s => (encS s).length) :=
    (hdrop k).of_enc_eq fun s => by
      obtain ⟨u, hs, hu⟩ := hh s
      rw [hu, hs, dropFrame_frame_append]
      rfl
  exact (h₁.append h₂ fun s => rfl).mono 2 (fun s => by omega) (fun s => by omega)

/-- **Case analysis on a sum component.** If `f` is computable on the left case and `g` on the
right case, so is the case analysis, within the bounds of the branch taken plus the length of the
encoded input. -/
private theorem sumElimSnd_tidy {f : π × α → ε} {g : π × β → ε} {Tf Sf : π × α → ℕ}
    {Tg Sg : π × β → ℕ}
    (hf : ComputableTidilyInO f (encPair encP encA) encE Tf Sf)
    (hg : ComputableTidilyInO g (encPair encP encB) encE Tg Sg) :
    ComputableTidilyInO
      (fun p : π × (α ⊕ β) => p.2.elim (fun a => f (p.1, a)) (fun b => g (p.1, b)))
      (encPair encP (encSum encA encB)) encE
      (fun p => (encPair encP (encSum encA encB) p).length +
        p.2.elim (fun a => Tf (p.1, a)) (fun b => Tg (p.1, b)))
      (fun p => (encPair encP (encSum encA encB) p).length +
        p.2.elim (fun a => Sf (p.1, a)) (fun b => Sg (p.1, b))) := by
  set enc := encPair encP (encSum encA encB)
  set F := fun p : π × (α ⊕ β) => p.2.elim (fun a => f (p.1, a)) (fun b => g (p.1, b))
  -- the test
  have htest : ComputableTidilyInO (fun p : π × (α ⊕ β) => p.2.isLeft) enc encBool
      (fun p => (enc p).length) (fun p => (enc p).length) := by
    refine ((ComputableInO.isLeft_deg encA encB).inO_one.tidy.comp
      (snd encP (encSum encA encB))).mono 2 (fun p => ?_) (fun p => ?_) <;>
    · simp only [enc, length_encPair]
      omega
  -- the two branches, on their cases
  let L : {p : π × (α ⊕ β) // p.2.isLeft = true} → π × α :=
    fun p => (p.1.1, p.1.2.getLeft (by simpa using p.2))
  let R : {p : π × (α ⊕ β) // p.2.isLeft = false} → π × β :=
    fun p => (p.1.1, p.1.2.getRight (by simpa using p.2))
  have hL := keepFrame_drop (encP := encP) (encA := encA)
    (encS := (Function.Embedding.subtype _).trans enc) (h := L) 1
    fun ⟨⟨x, s⟩, hs⟩ => by
      cases s with
      | inl a => exact ⟨false :: encA a, by simp [enc, L], rfl⟩
      | inr b => simp at hs
  have hR := keepFrame_drop (encP := encP) (encA := encB)
    (encS := (Function.Embedding.subtype _).trans enc) (h := R) 1
    fun ⟨⟨x, s⟩, hs⟩ => by
      cases s with
      | inl a => simp at hs
      | inr b => exact ⟨true :: encB b, by simp [enc, R], rfl⟩
  obtain ⟨c₀, h₀, -⟩ := htest
  obtain ⟨c₁, h₁, l₁⟩ := hf.comp hL
  obtain ⟨c₂, h₂, l₂⟩ := hg.comp hR
  have hF₁ : ∀ q : {p : π × (α ⊕ β) // p.2.isLeft = true}, F q.1 = (f ∘ L) q := by
    rintro ⟨⟨x, s⟩, hs⟩
    cases s with
    | inl a => rfl
    | inr b => simp at hs
  have hF₂ : ∀ q : {p : π × (α ⊕ β) // p.2.isLeft = false}, F q.1 = (g ∘ R) q := by
    rintro ⟨⟨x, s⟩, hs⟩
    cases s with
    | inl a => simp at hs
    | inr b => rfl
  let Tl : π × (α ⊕ β) → ℕ := fun p => p.2.elim (fun a => Tf (p.1, a)) (fun _ => 0)
  let Sl : π × (α ⊕ β) → ℕ := fun p => p.2.elim (fun a => Sf (p.1, a)) (fun _ => 0)
  let Tr : π × (α ⊕ β) → ℕ := fun p => p.2.elim (fun _ => 0) (fun b => Tg (p.1, b))
  let Sr : π × (α ⊕ β) → ℕ := fun p => p.2.elim (fun _ => 0) (fun b => Sg (p.1, b))
  have hlenL : ∀ q : {p : π × (α ⊕ β) // p.2.isLeft = true},
      ((Function.Embedding.subtype _).trans enc q).length = (enc q.1).length := fun _ => rfl
  have hlenR : ∀ q : {p : π × (α ⊕ β) // p.2.isLeft = false},
      ((Function.Embedding.subtype _).trans enc q).length = (enc q.1).length := fun _ => rfl
  obtain ⟨k, h⟩ := ComputableTidilyInTimeAndSpace.ite h₀ (f := F) (g := F)
    (tf := fun p => c₁ * ((enc p).length + Tl p + 1))
    (sf := fun p => c₁ * ((enc p).length + Sl p + 1))
    (tg := fun p => c₂ * ((enc p).length + Tr p + 1))
    (sg := fun p => c₂ * ((enc p).length + Sr p + 1))
    ((h₁.of_enc_eq fun q => by rw [Function.comp_apply, hF₁ q]).mono
      (fun ⟨⟨x, s⟩, hs⟩ => by
        cases s with
        | inl a => exact le_of_eq rfl
        | inr b => simp at hs)
      (fun ⟨⟨x, s⟩, hs⟩ => by
        cases s with
        | inl a => exact le_of_eq rfl
        | inr b => simp at hs))
    ((h₂.of_enc_eq fun q => by rw [Function.comp_apply, hF₂ q]).mono
      (fun ⟨⟨x, s⟩, hs⟩ => by
        cases s with
        | inl a => simp at hs
        | inr b => exact le_of_eq rfl)
      (fun ⟨⟨x, s⟩, hs⟩ => by
        cases s with
        | inl a => simp at hs
        | inr b => exact le_of_eq rfl))
  have hFeq : (fun x => if x.2.isLeft then F x else F x) = F := funext fun _ => by
    split_ifs <;> rfl
  rw [hFeq] at h
  refine of_bounds h (c₀ + c₁ + c₂ + k + 1) (fun p => ?_) (fun p => ?_) (fun p => ?_)
  · obtain ⟨x, s⟩ := p
    cases s <;> simp only [Tl, Tr, Sum.isLeft_inl, Sum.isLeft_inr, Sum.elim_inl, Sum.elim_inr,
      ite_true, ite_false, Bool.false_eq_true] <;> nlinarith
  · obtain ⟨x, s⟩ := p
    cases s <;> simp only [Sl, Sr, Sum.isLeft_inl, Sum.isLeft_inr, Sum.elim_inl, Sum.elim_inr,
      ite_true, ite_false, Bool.false_eq_true] <;> nlinarith
  · obtain ⟨x, s⟩ := p
    cases s with
    | inl a =>
      have := l₁ ⟨(x, .inl a), rfl⟩
      simp only [Function.comp_apply, L, Sum.getLeft_inl] at this
      simp only [F, Sum.elim_inl]
      nlinarith [hlenL ⟨(x, .inl a), rfl⟩]
    | inr b =>
      have := l₂ ⟨(x, .inr b), rfl⟩
      simp only [Function.comp_apply, R, Sum.getRight_inr] at this
      simp only [F, Sum.elim_inr]
      nlinarith [hlenR ⟨(x, .inr b), rfl⟩]

/-- **Case analysis on an option component.** If `f` is computable on the first component in the
`none` case and `g` on the pair in the `some` case, so is the case analysis, within the bounds of
the branch taken plus the length of the encoded input. -/
private theorem optionElimSnd_tidy {f : π → ε} {g : π × α → ε} {Tf Sf : π → ℕ} {Tg Sg : π × α → ℕ}
    (hf : ComputableTidilyInO f encP encE Tf Sf)
    (hg : ComputableTidilyInO g (encPair encP encA) encE Tg Sg) :
    ComputableTidilyInO (fun p : π × Option α => p.2.elim (f p.1) (fun a => g (p.1, a)))
      (encPair encP (encOption encA)) encE
      (fun p => (encPair encP (encOption encA) p).length +
        p.2.elim (Tf p.1) (fun a => Tg (p.1, a)))
      (fun p => (encPair encP (encOption encA) p).length +
        p.2.elim (Sf p.1) (fun a => Sg (p.1, a))) := by
  set enc := encPair encP (encOption encA)
  set F := fun p : π × Option α => p.2.elim (f p.1) (fun a => g (p.1, a))
  -- the test
  have htest : ComputableTidilyInO (fun p : π × Option α => p.2.isSome) enc encBool
      (fun p => (enc p).length) (fun p => (enc p).length) := by
    have he : ComputableTidilyInO (fun p : π × Option α => p.2.isNone) enc encBool
        (fun p => (enc p).length) (fun p => (enc p).length) := by
      have hd : ComputableTidilyInO (fun p : π × Option α => dropFrame (enc p)) enc encBits
          (fun p => (enc p).length) (fun p => (enc p).length) :=
        of_linear (.of_dropFrame fun p => rfl)
      refine ((of_linear (.of_isEmpty (f := List.isEmpty) (encIn := encBits) fun _ => rfl)).comp
        hd).of_enc_eq (fun p => ?_) |>.mono 2 (fun p => ?_) (fun p => ?_)
      · obtain ⟨x, _ | a⟩ := p <;> simp [enc, dropFrame_frame_append]
      all_goals
        simp only [enc, encPair_apply, dropFrame_frame_append, encBits,
          Function.Embedding.refl_apply, List.length_append, length_frame]
        omega
    refine ((ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool)
      Bool.not).inO_one.comp
      he).of_enc_eq (fun p => ?_) |>.mono 2 (fun p => ?_) (fun p => ?_)
    · obtain ⟨x, _ | a⟩ := p <;> rfl
    all_goals simp only [encBool_apply, List.length_singleton]; omega
  -- the two branches, on their cases
  let N : {p : π × Option α // p.2.isSome = false} → π := fun p => p.1.1
  let S : {p : π × Option α // p.2.isSome = true} → π × α :=
    fun p => (p.1.1, p.1.2.get p.2)
  have hN : ComputableTidilyInO N ((Function.Embedding.subtype _).trans enc) encP
      (fun s => ((Function.Embedding.subtype _).trans enc s).length)
      (fun s => ((Function.Embedding.subtype _).trans enc s).length) :=
    of_linear (.of_unframe fun ⟨⟨x, o⟩, _⟩ => by simp [enc, N, unframe_frame_append])
  have hS := keepFrame_drop (encP := encP) (encA := encA)
    (encS := (Function.Embedding.subtype _).trans enc) (h := S) 1
    fun ⟨⟨x, o⟩, ho⟩ => by
      cases o with
      | none => simp at ho
      | some a => exact ⟨true :: encA a, by simp [enc, S], rfl⟩
  obtain ⟨c₀, h₀, -⟩ := htest
  obtain ⟨c₁, h₁, l₁⟩ := hg.comp hS
  obtain ⟨c₂, h₂, l₂⟩ := hf.comp hN
  have hF₁ : ∀ q : {p : π × Option α // p.2.isSome = true}, F q.1 = (g ∘ S) q := by
    rintro ⟨⟨x, o⟩, ho⟩
    cases o with
    | none => simp at ho
    | some a => rfl
  have hF₂ : ∀ q : {p : π × Option α // p.2.isSome = false}, F q.1 = (f ∘ N) q := by
    rintro ⟨⟨x, o⟩, ho⟩
    cases o with
    | none => rfl
    | some a => simp at ho
  let Ts : π × Option α → ℕ := fun p => p.2.elim 0 (fun a => Tg (p.1, a))
  let Ss : π × Option α → ℕ := fun p => p.2.elim 0 (fun a => Sg (p.1, a))
  let Tn : π × Option α → ℕ := fun p => p.2.elim (Tf p.1) (fun _ => 0)
  let Sn : π × Option α → ℕ := fun p => p.2.elim (Sf p.1) (fun _ => 0)
  have hlenS : ∀ q : {p : π × Option α // p.2.isSome = true},
      ((Function.Embedding.subtype _).trans enc q).length = (enc q.1).length := fun _ => rfl
  have hlenN : ∀ q : {p : π × Option α // p.2.isSome = false},
      ((Function.Embedding.subtype _).trans enc q).length = (enc q.1).length := fun _ => rfl
  obtain ⟨k, h⟩ := ComputableTidilyInTimeAndSpace.ite h₀ (f := F) (g := F)
    (tf := fun p => c₁ * ((enc p).length + Ts p + 1))
    (sf := fun p => c₁ * ((enc p).length + Ss p + 1))
    (tg := fun p => c₂ * ((enc p).length + Tn p + 1))
    (sg := fun p => c₂ * ((enc p).length + Sn p + 1))
    ((h₁.of_enc_eq fun q => by rw [Function.comp_apply, hF₁ q]).mono
      (fun ⟨⟨x, o⟩, ho⟩ => by
        cases o with
        | none => simp at ho
        | some a => exact le_of_eq rfl)
      (fun ⟨⟨x, o⟩, ho⟩ => by
        cases o with
        | none => simp at ho
        | some a => exact le_of_eq rfl))
    ((h₂.of_enc_eq fun q => by rw [Function.comp_apply, hF₂ q]).mono
      (fun ⟨⟨x, o⟩, ho⟩ => by
        cases o with
        | none => exact le_of_eq rfl
        | some a => simp at ho)
      (fun ⟨⟨x, o⟩, ho⟩ => by
        cases o with
        | none => exact le_of_eq rfl
        | some a => simp at ho))
  have hFeq : (fun x => if x.2.isSome then F x else F x) = F := funext fun _ => by
    split_ifs <;> rfl
  rw [hFeq] at h
  refine of_bounds h (c₀ + c₁ + c₂ + k + 1) (fun p => ?_) (fun p => ?_) (fun p => ?_)
  · obtain ⟨x, o⟩ := p
    cases o <;> simp only [Ts, Tn, Option.isSome_none, Option.isSome_some, Option.elim_none,
      Option.elim_some, ite_true, ite_false, Bool.false_eq_true] <;> nlinarith
  · obtain ⟨x, o⟩ := p
    cases o <;> simp only [Ss, Sn, Option.isSome_none, Option.isSome_some, Option.elim_none,
      Option.elim_some, ite_true, ite_false, Bool.false_eq_true] <;> nlinarith
  · obtain ⟨x, o⟩ := p
    cases o with
    | none =>
      have := l₂ ⟨(x, none), rfl⟩
      simp only [Function.comp_apply, N] at this
      simp only [F, Option.elim_none]
      nlinarith [hlenN ⟨(x, none), rfl⟩]
    | some a =>
      have := l₁ ⟨(x, some a), rfl⟩
      simp only [Function.comp_apply, S, Option.get_some] at this
      simp only [F, Option.elim_some]
      nlinarith [hlenS ⟨(x, some a), rfl⟩]

end Turing.MultiTapeTM.ComputableTidilyInO

namespace Turing.MultiTapeTM.ComputableInO

variable {π α β ε : Type} {encP : π ↪ List Bool} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encE : ε ↪ List Bool}

/-- **Case analysis on a sum component.** If `f` is computable on the left case and `g` on the
right case, so is the case analysis, within the bounds of the branch taken plus the length of the
encoded input. -/
theorem sumElimSnd {f : π × α → ε} {g : π × β → ε} {Tf Sf : π × α → ℕ} {Tg Sg : π × β → ℕ}
    (hf : ComputableInO f (encPair encP encA) encE Tf Sf)
    (hg : ComputableInO g (encPair encP encB) encE Tg Sg) :
    ComputableInO
      (fun p : π × (α ⊕ β) => p.2.elim (fun a => f (p.1, a)) (fun b => g (p.1, b)))
      (encPair encP (encSum encA encB)) encE
      (fun p => (encPair encP (encSum encA encB) p).length +
        p.2.elim (fun a => Tf (p.1, a)) (fun b => Tg (p.1, b)))
      (fun p => (encPair encP (encSum encA encB) p).length +
        p.2.elim (fun a => Sf (p.1, a)) (fun b => Sg (p.1, b))) :=
  (ComputableTidilyInO.sumElimSnd_tidy hf.tidy hg.tidy).computableInO

/-- **Case analysis on an option component.** If `f` is computable on the first component in the
`none` case and `g` on the pair in the `some` case, so is the case analysis, within the bounds of
the branch taken plus the length of the encoded input. -/
theorem optionElimSnd {f : π → ε} {g : π × α → ε} {Tf Sf : π → ℕ} {Tg Sg : π × α → ℕ}
    (hf : ComputableInO f encP encE Tf Sf)
    (hg : ComputableInO g (encPair encP encA) encE Tg Sg) :
    ComputableInO (fun p : π × Option α => p.2.elim (f p.1) (fun a => g (p.1, a)))
      (encPair encP (encOption encA)) encE
      (fun p => (encPair encP (encOption encA) p).length +
        p.2.elim (Tf p.1) (fun a => Tg (p.1, a)))
      (fun p => (encPair encP (encOption encA) p).length +
        p.2.elim (Sf p.1) (fun a => Sg (p.1, a))) :=
  (ComputableTidilyInO.optionElimSnd_tidy hf.tidy hg.tidy).computableInO

end Turing.MultiTapeTM.ComputableInO
