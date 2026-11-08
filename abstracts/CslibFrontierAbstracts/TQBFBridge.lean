/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontier.Computability.Complexity.Classes.Space.TQBF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Bridge for the TQBF formal abstract (Pattern B: polymorphic presentation)

Transfers `Cslib.Complexity.TQBF_pspaceComplete` to the independent `inductive Formula` presentation
in `TQBFAbstract.lean`. Because `toFormula` is surjective and preserves the binary token encoding
`encode`, it is automatically a bijection between `Cslib.Logic.PL.QBF ℕ` and the abstract's
`Formula`, and the Turing machines for `TQBF ∈ PSPACE` and `PSPACE`-hardness operate on identical
bitstrings.
-/

namespace ComplexityTests.Abstracts.TQBFBridge

open Turing Turing.MultiTapeTM Cslib.Logic.PL Cslib.Complexity

/-- Framing a bitstring by doubling each bit `b` as `[true, b]` and terminating with `[false]`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Encoding a pair by framing the first component followed by the second. -/
def encodePair {α β : Type} (encA : α → List Bool) (encB : β → List Bool) (p : α × β) :
    List Bool :=
  frame (encA p.1) ++ encB p.2

/-- Encoding a list by concatenating the framed encodings of its elements. -/
def encodeList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (frame ∘ enc)

/-- Encoding a prefix-order token `(kind, var)` with `kind` in unary and `var` in binary. -/
def encodeToken : ℕ × ℕ → List Bool :=
  encodePair (fun k => List.replicate k true) Nat.bits

/-- Polymorphic signature of an abstract presentation of Quantified Boolean Formulas. -/
structure Presentation where
  Formula : Type
  var : ℕ → Formula
  top : Formula
  bot : Formula
  not : Formula → Formula
  and : Formula → Formula → Formula
  or : Formula → Formula → Formula
  ex : ℕ → Formula → Formula
  all : ℕ → Formula → Formula
  formula_induction {P : Formula → Prop} :
    (∀ v, P (var v)) → P top → P bot →
    (∀ φ, P φ → P (not φ)) →
    (∀ φ ψ, P φ → P ψ → P (and φ ψ)) →
    (∀ φ ψ, P φ → P ψ → P (or φ ψ)) →
    (∀ v φ, P φ → P (ex v φ)) →
    (∀ v φ, P φ → P (all v φ)) →
    ∀ φ, P φ
  eval : (ℕ → Bool) → Formula → Bool
  freeVars : Formula → Finset ℕ
  tokens : Formula → List (ℕ × ℕ)

/-- Equational specification for a QBF presentation. -/
structure Laws (S : Presentation) : Prop where
  eval_var : ∀ σ v, S.eval σ (S.var v) = σ v
  eval_top : ∀ σ, S.eval σ S.top = true
  eval_bot : ∀ σ, S.eval σ S.bot = false
  eval_not : ∀ σ φ, S.eval σ (S.not φ) = !S.eval σ φ
  eval_and : ∀ σ φ ψ, S.eval σ (S.and φ ψ) = (S.eval σ φ && S.eval σ ψ)
  eval_or : ∀ σ φ ψ, S.eval σ (S.or φ ψ) = (S.eval σ φ || S.eval σ ψ)
  eval_ex : ∀ σ v φ,
    S.eval σ (S.ex v φ) =
      (S.eval (Function.update σ v false) φ || S.eval (Function.update σ v true) φ)
  eval_all : ∀ σ v φ,
    S.eval σ (S.all v φ) =
      (S.eval (Function.update σ v false) φ && S.eval (Function.update σ v true) φ)
  freeVars_var : ∀ v, S.freeVars (S.var v) = {v}
  freeVars_top : S.freeVars S.top = ∅
  freeVars_bot : S.freeVars S.bot = ∅
  freeVars_not : ∀ φ, S.freeVars (S.not φ) = S.freeVars φ
  freeVars_and : ∀ φ ψ, S.freeVars (S.and φ ψ) = S.freeVars φ ∪ S.freeVars ψ
  freeVars_or : ∀ φ ψ, S.freeVars (S.or φ ψ) = S.freeVars φ ∪ S.freeVars ψ
  freeVars_ex : ∀ v φ, S.freeVars (S.ex v φ) = (S.freeVars φ).erase v
  freeVars_all : ∀ v φ, S.freeVars (S.all v φ) = (S.freeVars φ).erase v
  tokens_var : ∀ v, S.tokens (S.var v) = [(0, v)]
  tokens_top : S.tokens S.top = [(1, 0)]
  tokens_bot : S.tokens S.bot = [(2, 0)]
  tokens_not : ∀ φ, S.tokens (S.not φ) = (3, 0) :: S.tokens φ
  tokens_and : ∀ φ ψ, S.tokens (S.and φ ψ) = (4, 0) :: (S.tokens φ ++ S.tokens ψ)
  tokens_or : ∀ φ ψ, S.tokens (S.or φ ψ) = (5, 0) :: (S.tokens φ ++ S.tokens ψ)
  tokens_ex : ∀ v φ, S.tokens (S.ex v φ) = (6, v) :: S.tokens φ
  tokens_all : ∀ v φ, S.tokens (S.all v φ) = (7, v) :: S.tokens φ

/-- Translate an internal `QBF ℕ` formula into the abstract presentation `S`. -/
def toFormula (S : Presentation) : QBF ℕ → S.Formula
  | .var v => S.var v
  | .top => S.top
  | .bot => S.bot
  | .not φ => S.not (toFormula S φ)
  | .and φ ψ => S.and (toFormula S φ) (toFormula S ψ)
  | .or φ ψ => S.or (toFormula S φ) (toFormula S ψ)
  | .ex v φ => S.ex v (toFormula S φ)
  | .all v φ => S.all v (toFormula S φ)

theorem toFormula_surjective (S : Presentation) : Function.Surjective (toFormula S) := by
  intro p
  refine S.formula_induction (P := fun p => ∃ φ, toFormula S φ = p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p
  · intro v; exact ⟨.var v, rfl⟩
  · exact ⟨.top, rfl⟩
  · exact ⟨.bot, rfl⟩
  · rintro φ ⟨φ', rfl⟩; exact ⟨.not φ', rfl⟩
  · rintro φ ψ ⟨φ', rfl⟩ ⟨ψ', rfl⟩; exact ⟨.and φ' ψ', rfl⟩
  · rintro φ ψ ⟨φ', rfl⟩ ⟨ψ', rfl⟩; exact ⟨.or φ' ψ', rfl⟩
  · rintro v φ ⟨φ', rfl⟩; exact ⟨.ex v φ', rfl⟩
  · rintro v φ ⟨φ', rfl⟩; exact ⟨.all v φ', rfl⟩

theorem eval_toFormula (S : Presentation) (h : Laws S) (φ : QBF ℕ) (σ : ℕ → Bool) :
    S.eval σ (toFormula S φ) = φ.eval σ := by
  induction φ generalizing σ <;> simp_all [toFormula, QBF.eval,
    h.eval_var, h.eval_top, h.eval_bot, h.eval_not, h.eval_and, h.eval_or, h.eval_ex, h.eval_all]

theorem freeVars_toFormula (S : Presentation) (h : Laws S) (φ : QBF ℕ) :
    S.freeVars (toFormula S φ) = φ.freeVars := by
  induction φ <;> simp_all [toFormula, QBF.freeVars,
    h.freeVars_var, h.freeVars_top, h.freeVars_bot, h.freeVars_not,
    h.freeVars_and, h.freeVars_or, h.freeVars_ex, h.freeVars_all]

theorem tokens_toFormula (S : Presentation) (h : Laws S) (φ : QBF ℕ) :
    S.tokens (toFormula S φ) = φ.tokens.map (fun t => (TQBF.kindIndex t.1, t.2)) := by
  induction φ <;> simp_all [toFormula, QBF.tokens, TQBF.kindIndex,
    h.tokens_var, h.tokens_top, h.tokens_bot, h.tokens_not,
    h.tokens_and, h.tokens_or, h.tokens_ex, h.tokens_all]

/-- Binary encoding of a formula in presentation `S`. -/
def encodeQBF (S : Presentation) (p : S.Formula) : List Bool :=
  encodeList encodeToken (S.tokens p)

theorem encodeQBF_toFormula (S : Presentation) (h : Laws S) (φ : QBF ℕ) :
    encodeQBF S (toFormula S φ) = Cslib.Complexity.encQBF φ := by
  simp only [encodeQBF, tokens_toFormula S h, Cslib.Complexity.encQBF_apply,
    encodeList, Turing.MultiTapeTM.encList, List.flatMap_map]
  rfl

theorem toFormula_injective (S : Presentation) (h : Laws S) :
    Function.Injective (toFormula S) := by
  intro φ ψ hEq
  apply Cslib.Complexity.encQBF.injective
  rw [← encodeQBF_toFormula S h φ, ← encodeQBF_toFormula S h ψ, hEq]

theorem encodeQBF_injective (S : Presentation) (h : Laws S) :
    Function.Injective (encodeQBF S) := by
  intro p q hpq
  obtain ⟨φ, rfl⟩ := toFormula_surjective S p
  obtain ⟨ψ, rfl⟩ := toFormula_surjective S q
  rw [encodeQBF_toFormula S h, encodeQBF_toFormula S h] at hpq
  rw [Cslib.Complexity.encQBF.injective hpq]

/-- Injective embedding of `S.Formula` into bitstrings. -/
def encQBF (S : Presentation) (h : Laws S) : S.Formula ↪ List Bool :=
  ⟨encodeQBF S, encodeQBF_injective S h⟩

/-- Plain polynomial-time computability in terms of upstream `Cslib` multi-tape Turing machines. -/
def ComputableInPolyTime {α β : Type} (f : α → β)
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f encA encB t s

/-- Polynomial-time many-one reducibility using plain polynomial-time computability. -/
def PolyTimeReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, ComputableInPolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- Deterministic polynomial space (`PSPACE`) in terms of upstream `Cslib` Turing machines. -/
def PSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (t : α → ℕ) (s : ℕ → ℕ),
    Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpace f enc
      ⟨fun b => [b], by intro a b h; injection h⟩
      t (fun a => s (enc a).length) ∧
    ∀ a, a ∈ A ↔ f a = true}

theorem mem_PSPACE_iff {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ PSPACE enc ↔ A ∈ Cslib.Complexity.PSPACE enc := by
  constructor
  · rintro ⟨f, t, s, hs, hf, hA⟩
    exact ⟨f, ⟨t, fun a => s (enc a).length, ⟨s, hs, fun _ => le_rfl⟩, hf⟩, hA⟩
  · rintro ⟨f, ⟨t, s', ⟨s, hs, hle⟩, hf⟩, hA⟩
    exact ⟨f, t, s, hs, hf.mono (fun _ => le_rfl) hle, hA⟩

theorem mem_TQBF_toFormula_iff (S : Presentation) (h : Laws S) (φ : QBF ℕ) :
    (S.freeVars (toFormula S φ) = ∅ ∧ S.eval (fun _ => false) (toFormula S φ) = true) ↔
      φ ∈ Cslib.Complexity.TQBF := by
  rw [freeVars_toFormula S h, eval_toFormula S h, Cslib.Complexity.mem_TQBF, QBF.Closed]

/-- Transfer of `TQBF ∈ PSPACE` to presentation `S`. -/
theorem tqbf_mem_PSPACE (S : Presentation) (h : Laws S) :
    {p : S.Formula | S.freeVars p = ∅ ∧ S.eval (fun _ => false) p = true} ∈
      PSPACE (encQBF S h) := by
  classical
  let e : QBF ℕ ≃ S.Formula :=
    Equiv.ofBijective (toFormula S) ⟨toFormula_injective S h, toFormula_surjective S⟩
  have hmem : Cslib.Complexity.TQBF ∈ PSPACE Cslib.Complexity.encQBF :=
    mem_PSPACE_iff.mpr Cslib.Complexity.TQBF_mem_PSPACE
  rcases hmem with ⟨f, t, s, hs, ⟨k, State, hfin, tm, htm⟩, hA⟩
  refine ⟨fun p => f (e.symm p), fun p => t (e.symm p), s, hs,
    ⟨k, State, hfin, tm, fun p => ?_⟩, fun p => ?_⟩
  · have hp : encodeQBF S p = Cslib.Complexity.encQBF (e.symm p) := by
      conv_lhs => rw [← e.apply_symm_apply p]
      exact encodeQBF_toFormula S h (e.symm p)
    simpa [encQBF, hp] using htm (e.symm p)
  · conv_lhs => rw [show p = toFormula S (e.symm p) from (e.apply_symm_apply p).symm]
    exact (mem_TQBF_toFormula_iff S h (e.symm p)).trans (hA (e.symm p))

/-- Transfer of `TQBF` PSPACE-hardness to presentation `S`. -/
theorem tqbf_pspaceHard (S : Presentation) (h : Laws S) :
    ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
      A ∈ PSPACE encA →
        PolyTimeReducible encA (encQBF S h) A
          {p : S.Formula | S.freeVars p = ∅ ∧ S.eval (fun _ => false) p = true} := by
  intro α encA A hA
  obtain ⟨f, hf, hiff⟩ := Cslib.Complexity.TQBF_pspaceHard encA A (mem_PSPACE_iff.mp hA)
  obtain ⟨t, s, ht, hs, k, State, hfin, tm, htm⟩ := hf
  refine ⟨fun a => toFormula S (f a), ⟨t, s, ht, hs, k, State, hfin, tm, fun a => ?_⟩, fun a => ?_⟩
  · simpa [encQBF, encodeQBF_toFormula S h (f a)] using htm a
  · exact (hiff a).trans (mem_TQBF_toFormula_iff S h (f a)).symm

/-- Transfer of `TQBF` PSPACE-completeness to presentation `S`. -/
theorem tqbf_pspaceComplete (S : Presentation) (h : Laws S) :
    {p : S.Formula | S.freeVars p = ∅ ∧ S.eval (fun _ => false) p = true} ∈ PSPACE (encQBF S h) ∧
    ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
      A ∈ PSPACE encA →
        PolyTimeReducible encA (encQBF S h) A
          {p : S.Formula | S.freeVars p = ∅ ∧ S.eval (fun _ => false) p = true} :=
  ⟨tqbf_mem_PSPACE S h, tqbf_pspaceHard S h⟩

end ComplexityTests.Abstracts.TQBFBridge
