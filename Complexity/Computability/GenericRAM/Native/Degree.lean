/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native
public import Complexity.Computability.GenericRAM.Native.Combinators

/-!
# Native certificates with explicit polynomial degrees

`NativeCertificate.IsPolynomial` says that a certificate's time and space bounds are polynomial in
the encoded input length, without naming a degree. `NativeCertificate.HasDegree c d` names it: the
time and space bounds are at most a constant times `(n + 1) ^ d` on encoded inputs of length `n`,
and the encoded output has linear length. Linear output is what keeps the degree from growing under
composition: a degree-`d` bound evaluated at a linearly long intermediate value is again of degree
`d`. This is the discipline of `Turing.MultiTapeTM.ComputableInDegree` with output degree one,
applied to the input-dependent bounds that certificates carry.

Every certificate combinator preserves `HasDegree`, so a simulation assembled from them inherits an
explicit degree from its primitives. `Model.NativePrimitives.HasDegree` asks the same of all
primitive certificates of a RAM model.

## Main definitions

* `Cslib.GenericRAM.NativeCertificate.HasDegree`: time and space bounds of degree `d`, encoded
  output of linear length.
* `Cslib.GenericRAM.NativeCertificate.ofDegree`: the certificate of a degree-`d` computation with
  linear output.
* `Cslib.GenericRAM.Model.NativePrimitives.HasDegree`: every primitive certificate has degree `d`.

## Main results

* `Cslib.GenericRAM.NativeCertificate.HasDegree.isPolynomial`: a degree bound is polynomial.
* `Cslib.GenericRAM.NativeCertificate.comp_hasDegree`, `.prod_hasDegree`, `.branch_hasDegree`,
  `.option_hasDegree` and the other `*_hasDegree` lemmas: the combinators preserve the degree.
-/

@[expose] public section

namespace Cslib.GenericRAM.NativeCertificate

open Turing.MultiTapeTM

variable {α β γ δ : Type} {ei : α ↪ List Bool} {em : β ↪ List Bool}
  {eo : γ ↪ List Bool} {f : α → β} {g : α → γ} {d d' : ℕ}

/-- Time and space bounds of degree `d`, and encoded output of linear length, in the encoded input
length. -/
structure HasDegree (c : NativeCertificate f ei em) (d : ℕ) : Prop where
  /-- The time bound has degree `d`. -/
  time : DegreeBounded (fun a => (ei a).length) c.time d
  /-- The space bound has degree `d`. -/
  space : DegreeBounded (fun a => (ei a).length) c.space d
  /-- The encoded output has linear length. -/
  length : DegreeBounded (fun a => (ei a).length) (fun a => (em (f a)).length) 1

namespace HasDegree

variable {c : NativeCertificate f ei em}

/-- Raising the degree keeps the bound. -/
theorem mono (h : c.HasDegree d) (hd : d ≤ d') : c.HasDegree d' :=
  ⟨h.time.mono_deg hd, h.space.mono_deg hd, h.length⟩

/-- A certificate of some degree is polynomial. -/
theorem isPolynomial (h : c.HasDegree d) : c.IsPolynomial :=
  ⟨h.time.polyBounded, h.space.polyBounded⟩

/-- Transfer a degree to a certificate with the same bounds for a pointwise equal function. This
sees through certificates defined by case analysis, whose casts block unification. -/
theorem of_eq {f' : α → β} (c' : NativeCertificate f' ei em) (h : c.HasDegree d)
    (ht : c'.time = c.time) (hs : c'.space = c.space) (hf : ∀ a, f a = f' a) :
    c'.HasDegree d :=
  ⟨ht ▸ h.time, hs ▸ h.space, h.length.mono fun a => by rw [hf a]⟩

end HasDegree

/-- A degree-`d` bound evaluated at an intermediate value of linear length has degree `d`. -/
theorem degreeBounded_comp {size : α → ℕ} {u : β → ℕ}
    (hu : DegreeBounded (fun b => (em b).length) u d)
    (hf : DegreeBounded size (fun a => (em (f a)).length) 1) :
    DegreeBounded size (fun a => u (f a)) d := by
  simpa only [one_mul] using hu.comp hf

/-- A linear-time, linear-space computation has encoded output of linear length. -/
theorem length_of_linear {h : β → γ}
    (hh : ComputableInO h em eo (fun b => (em b).length) (fun b => (em b).length)) :
    DegreeBounded (fun b => (em b).length) (fun b => (eo (h b)).length) 1 := by
  obtain ⟨k, -, hl⟩ := hh
  exact ⟨k, fun b => by simpa only [pow_one] using hl b⟩

/-- A certificate with linear space has encoded output of linear length. -/
theorem length_of_space (c : NativeCertificate f ei em)
    (hs : DegreeBounded (fun a => (ei a).length) c.space 1) :
    DegreeBounded (fun a => (ei a).length) (fun a => (em (f a)).length) 1 := by
  obtain ⟨k, -, hl⟩ := c.computes
  obtain ⟨C, hC⟩ := hs
  refine ⟨k * (C + 1), fun a => (hl a).trans ?_⟩
  have := hC a
  simp only [pow_one] at this ⊢
  nlinarith

/-- A certificate whose time has degree `d ≥ 1` and whose space is linear has degree `d`. -/
theorem hasDegree_of_space_linear (c : NativeCertificate f ei em)
    (ht : DegreeBounded (fun a => (ei a).length) c.time d)
    (hs : DegreeBounded (fun a => (ei a).length) c.space 1) (hd : 1 ≤ d) : c.HasDegree d :=
  ⟨ht, hs.mono_deg hd, c.length_of_space hs⟩

/-- The certificate of a computation in time and space degree `d` with linear output. -/
def ofDegree (h : ComputableInDegree f ei em d 1) : NativeCertificate f ei em :=
  ⟨fun a => ((ei a).length + 1) ^ d, fun a => ((ei a).length + 1) ^ d, h.inO⟩

@[simp] theorem ofDegree_time (h : ComputableInDegree f ei em d 1) (a : α) :
    (ofDegree h).time a = ((ei a).length + 1) ^ d := rfl

@[simp] theorem ofDegree_space (h : ComputableInDegree f ei em d 1) (a : α) :
    (ofDegree h).space a = ((ei a).length + 1) ^ d := rfl

/-- `ofDegree` keeps the degree of the computation. -/
theorem ofDegree_hasDegree (h : ComputableInDegree f ei em d 1) : (ofDegree h).HasDegree d :=
  ⟨⟨1, fun a => by simp⟩, ⟨1, fun a => by simp⟩, h.2⟩

/-! ## The combinators preserve the degree -/

theorem linear_hasDegree
    (h : ComputableInO f ei em (fun a => (ei a).length) (fun a => (ei a).length)) (hd : 1 ≤ d) :
    (linear h).HasDegree d :=
  ⟨DegreeBounded.self.mono_deg hd, DegreeBounded.self.mono_deg hd, length_of_linear h⟩

theorem const_hasDegree (b : β) (hd : 1 ≤ d) : (const (ei := ei) (em := em) b).HasDegree d :=
  linear_hasDegree _ hd

theorem comp_hasDegree {h : β → γ} (c' : NativeCertificate h em eo)
    (c : NativeCertificate f ei em) (hc' : c'.HasDegree d) (hc : c.HasDegree d) :
    (c'.comp c).HasDegree d :=
  ⟨hc.time.add (degreeBounded_comp hc'.time hc.length),
    hc.space.add (degreeBounded_comp hc'.space hc.length),
    degreeBounded_comp (f := f) hc'.length hc.length⟩

theorem prod_hasDegree (c : NativeCertificate f ei em) (c' : NativeCertificate g ei eo)
    (hc : c.HasDegree d) (hc' : c'.HasDegree d) : (prod c c').HasDegree d :=
  ⟨hc.time.add hc'.time, hc.space.add hc'.space,
    ((hc.length.smul 2).add_const 1 |>.add hc'.length).mono fun a => by
      simp only [length_encPair, le_refl]⟩

theorem post_hasDegree {h : β → γ} (c : NativeCertificate f ei em)
    (hh : ComputableInO h em eo (fun b => (em b).length) (fun b => (em b).length))
    (hc : c.HasDegree d) : (post c hh).HasDegree d :=
  ⟨hc.time, hc.space, degreeBounded_comp (f := f) (length_of_linear hh) hc.length⟩

theorem fst_hasDegree {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo))
    (hc : c.HasDegree d) : (fst c).HasDegree d :=
  post_hasDegree c _ hc

theorem snd_hasDegree {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo))
    (hc : c.HasDegree d) : (snd c).HasDegree d :=
  post_hasDegree c _ hc

theorem some_hasDegree (c : NativeCertificate f ei em) (hc : c.HasDegree d) :
    (some c).HasDegree d :=
  post_hasDegree c _ hc

theorem inl_hasDegree (c : NativeCertificate f ei em) (right : γ ↪ List Bool)
    (hc : c.HasDegree d) : (inl c right).HasDegree d :=
  post_hasDegree c _ hc

theorem inr_hasDegree (left : γ ↪ List Bool) (c : NativeCertificate f ei em)
    (hc : c.HasDegree d) : (inr left c).HasDegree d :=
  post_hasDegree c _ hc

theorem congr_hasDegree {f' : α → β} (c : NativeCertificate f ei em) (h : ∀ a, f a = f' a)
    (hc : c.HasDegree d) : (congr c h).HasDegree d :=
  ⟨hc.time, hc.space, hc.length.mono fun a => by rw [← h a]⟩

theorem pull_hasDegree {ed : δ ↪ List Bool} (c : NativeCertificate f ei em)
    (hc : c.HasDegree d) (hd : 1 ≤ d) : (pull c ed).HasDegree d :=
  comp_hasDegree c _ hc (linear_hasDegree _ hd)

theorem payload_hasDegree (input : α ↪ List Bool) (out : β ↪ List Bool) (hd : 1 ≤ d) :
    (payload input out).HasDegree d :=
  linear_hasDegree _ hd

theorem branch_hasDegree {condition : α → Bool} {f₁ f₂ : α → β}
    (test : NativeCertificate condition ei encBool)
    (yes : NativeCertificate f₁ ei em) (no : NativeCertificate f₂ ei em)
    (ht : test.HasDegree d) (hy : yes.HasDegree d) (hn : no.HasDegree d) :
    (branch test yes no).HasDegree d := by
  refine ⟨(ht.time.add (hy.time.add hn.time)).mono fun a => ?_,
    (ht.space.add (hy.space.add hn.space)).mono fun a => ?_,
    (hy.length.add hn.length).mono fun a => ?_⟩
  · simp only [branch_time]; split <;> omega
  · simp only [branch_space]; split <;> omega
  · split <;> omega

theorem option_hasDegree {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    (c : NativeCertificate value ei (encOption em))
    (no : NativeCertificate fallback ei eo)
    (yes : NativeCertificate body (encPair ei em) eo)
    (hc : c.HasDegree d) (hno : no.HasDegree d) (hyes : yes.HasDegree d) (hd : 1 ≤ d) :
    (option c no yes).HasDegree d := by
  -- The continuation's input `(a, b)` is linearly long when `value a = some b`.
  have hL : DegreeBounded (fun a => (ei a).length)
      (fun a => 2 * (ei a).length + (encOption em (value a)).length) 1 :=
    (DegreeBounded.self.smul 2).add hc.length
  have hpair (a : α) (b : β) (hv : value a = Option.some b) :
      (encPair ei em (a, b)).length = 2 * (ei a).length + (encOption em (value a)).length := by
    rw [hv]; simp; omega
  -- A bound `C (|(a, b)| + 1) ^ k` on the continuation is of degree `k` in `|ei a|`.
  have hsub {k C : ℕ} : DegreeBounded (fun a => (ei a).length)
      (fun a => C * (2 * (ei a).length + (encOption em (value a)).length + 1) ^ k) k := by
    simpa only [one_mul] using DegreeBounded.comp (size' := id)
      (v := fun n => C * (n + 1) ^ k) ⟨C, fun _ => le_rfl⟩ hL
  obtain ⟨ct, hyt⟩ := hyes.time
  obtain ⟨cs, hys⟩ := hyes.space
  obtain ⟨cl, hyl⟩ := hyes.length
  refine ⟨((hc.time.smul 2).add (DegreeBounded.self.mono_deg hd) |>.add
      (hno.time.add (hsub (C := ct)))).mono fun a => ?_,
    ((hc.space.smul 2).add (DegreeBounded.self.mono_deg hd) |>.add
      (hno.space.add (hsub (C := cs)))).mono fun a => ?_,
    (hno.length.add (hsub (C := cl))).mono fun a => ?_⟩
  · simp only [option_time]
    cases hv : value a with
    | none => simp
    | some b =>
      have := hyt (a, b)
      dsimp only at this
      rw [hpair a b hv, hv] at this
      simp only [Option.elim_some]
      omega
  · simp only [option_space]
    cases hv : value a with
    | none => simp
    | some b =>
      have := hys (a, b)
      dsimp only at this
      rw [hpair a b hv, hv] at this
      simp only [Option.elim_some]
      omega
  · cases hv : value a with
    | none => simp
    | some b =>
      have := hyl (a, b)
      dsimp only at this
      rw [hpair a b hv, hv] at this
      simp only [Option.elim_some, pow_one] at this ⊢
      omega

end Cslib.GenericRAM.NativeCertificate

namespace Cslib.GenericRAM.Model

/-- Every primitive certificate of the bundle has degree `d`. -/
structure NativePrimitives.HasDegree {M : Model.{0, 0, 0, 0}} {enc : M.Encoding}
    (N : M.NativePrimitives enc) (d : ℕ) : Prop where
  /-- Every literal symbol's certificate has degree `d`. -/
  constant : ∀ c, (N.constant c).HasDegree d
  /-- Every operation symbol's certificate has degree `d`. -/
  operation : ∀ op, (N.operation op).HasDegree d
  /-- Every test symbol's certificate has degree `d`. -/
  test : ∀ t, (N.test t).HasDegree d
  /-- The address extraction certificate has degree `d`. -/
  address : N.address.HasDegree d
  /-- The move validation certificate has degree `d`. -/
  validMove : N.validMove.HasDegree d
  /-- The control-label validation certificate has degree `d`. -/
  validPC : N.validPC.HasDegree d

/-- Raising the degree of a primitive bundle keeps the bound. -/
theorem NativePrimitives.HasDegree.mono {M : Model.{0, 0, 0, 0}} {enc : M.Encoding}
    {N : M.NativePrimitives enc} {d d' : ℕ} (h : N.HasDegree d) (hd : d ≤ d') :
    N.HasDegree d' :=
  ⟨fun c => (h.constant c).mono hd, fun op => (h.operation op).mono hd,
    fun t => (h.test t).mono hd, h.address.mono hd, h.validMove.mono hd, h.validPC.mono hd⟩

end Cslib.GenericRAM.Model
