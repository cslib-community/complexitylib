/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.FoldCompiler
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile

/-! # Legacy fold certificate facade

The machine construction lives in the Internal fold compiler. This compatibility theorem retains
its original statement for callers still using the staged existential tidy interface.
-/
namespace Turing.MultiTapeTM
universe u
public theorem ComputableTidilyInTimeAndSpace.foldl {γ α β : Type u} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
    {encO : Option (List α × β) ↪ List Bool}
    [hLE : ListEncoding encA encL] [hBA : PairEncoding encB encA encBA]
    [hSE : PairEncoding encL encB encS] [hOE : OptionEncoding encS encO]
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    {t s : γ → ℕ} {tStep sStep : β × α → ℕ} {tMax sMax lMax : γ → ℕ}
    (hlist : ComputableTidilyInTimeAndSpace list encIn encL t s)
    (hinit : ComputableTidilyInTimeAndSpace init encIn encB t s)
    (hstep : ComputableTidilyInTimeAndSpace (fun p : β × α => step p.1 p.2) encBA encB tStep sStep)
    (htMax : ∀ x i (hi : i < (list x).length),
      tStep (((list x).take i).foldl step (init x), (list x)[i]) ≤ tMax x)
    (hsMax : ∀ x i (hi : i < (list x).length),
      sStep (((list x).take i).foldl step (init x), (list x)[i]) ≤ sMax x)
    (hlMax : ∀ x, ∀ i ≤ (list x).length,
      (encS ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun x => (list x).foldl step (init x)) encIn encB
      (fun x => c * (t x + ((list x).length + 1) * (tMax x + lMax x + 1)))
      (fun x => c * (s x + sMax x + lMax x + 1)) := by
  obtain ⟨kl, Ql, _, tml, hl⟩ := hlist
  obtain ⟨ki, Qi, _, tmi, hi⟩ := hinit
  obtain ⟨ks, Qs, _, tms, hs⟩ := hstep
  exact Internal.FoldCompiler.foldl (encA := encA) (encL := encL)
    (encS := encS) (encO := encO) hl hi hs htMax hsMax hlMax
end Turing.MultiTapeTM
