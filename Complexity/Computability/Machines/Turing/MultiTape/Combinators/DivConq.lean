/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.StackLoop

/-!
# Divide and conquer

A divide-and-conquer recursion (`Turing.MultiTapeTM.DivConq`) solves a base problem directly and
otherwise solves a first subproblem, derives a second subproblem and some saved data from the
problem and the first solution, solves the second subproblem, and combines the saved data with the
second solution. Its evaluation with a cost is the inductive relation
`Turing.MultiTapeTM.DivConq.Eval`: a node costs its two subproblems plus a cost of its own.

If the parts are tidily computable, the solution is tidily computable within the cost of the
evaluation, when the cost of every node covers the costs of its parts and the lengths of the words
it touches (`Turing.MultiTapeTM.ComputableTidilyInO.divConq`). The machine runs the recursion as a
`Turing.MultiTapeTM.StackLoop`, keeping the pending problems and saved data on a stack, so a node
does not pay for the frames of its ancestors.

## Main definitions

* `Turing.MultiTapeTM.DivConq`: the parts of a divide-and-conquer recursion.
* `Turing.MultiTapeTM.DivConq.Eval`: evaluation with a cost.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInO.divConq`: divide and conquer within the cost of the
  evaluation.
-/

public section

namespace Turing.MultiTapeTM

/-- The parts of a divide-and-conquer recursion: a test for base problems, their solutions, the
first subproblem, the second subproblem and saved data from the problem and the first solution,
and the solution from the saved data and the second solution. -/
structure DivConq (α β γ : Type) where
  /-- Whether a problem is solved directly. -/
  isBase : α → Bool
  /-- The solution of a base problem. -/
  base : α → β
  /-- The first subproblem. -/
  left : α → α
  /-- The second subproblem and the saved data, from the problem and the first solution. -/
  mid : α × β → α × γ
  /-- The solution, from the saved data and the second solution. -/
  join : γ × β → β

namespace DivConq

variable {α β γ : Type}

/-- `D.Eval cb cn a b c`: the recursion solves `a` with `b`, at cost `c`, where a base problem `a`
costs `cb a` and a node `a` with solutions `b₁` and `b₂` of its subproblems costs `cn a b₁ b₂` on
top of its subproblems. -/
inductive Eval (D : DivConq α β γ) (cb : α → ℕ) (cn : α → β → β → ℕ) : α → β → ℕ → Prop
  /-- A base problem. -/
  | base {a : α} : D.isBase a = true → Eval D cb cn a (D.base a) (cb a)
  /-- A node: the first subproblem, then the second. -/
  | node {a : α} {b₁ b₂ : β} {c₁ c₂ : ℕ} : D.isBase a = false →
      Eval D cb cn (D.left a) b₁ c₁ → Eval D cb cn (D.mid (a, b₁)).1 b₂ c₂ →
      Eval D cb cn a (D.join ((D.mid (a, b₁)).2, b₂)) (c₁ + c₂ + cn a b₁ b₂)

end DivConq

/-- **Divide and conquer.** If the parts of a divide-and-conquer recursion are tidily computable
and every input `x` is solved with `F x` at cost `C x`, then `F` is tidily computable within the
cost of the evaluation plus the initialization. The cost of a base problem must cover its test,
its solution and the lengths of the problem and its solution; the cost of a node must cover its
test, the first subproblem, the middle and the combination, and the lengths of all the values they
read and write. -/
theorem ComputableTidilyInO.divConq {δ α β γ : Type} {encIn : δ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encG : γ ↪ List Bool} (D : DivConq α β γ)
    {init : δ → α} {F : δ → β} {C : δ → ℕ} {cb : α → ℕ} {cn : α → β → β → ℕ}
    {Ti Si : δ → ℕ} {Tt St Tb Sb Tl Sl : α → ℕ} {Tm Sm : α × β → ℕ} {Tj Sj : γ × β → ℕ}
    (hinit : ComputableTidilyInO init encIn encA Ti Si)
    (hisBase : ComputableTidilyInO D.isBase encA encBool Tt St)
    (hbase : ComputableTidilyInO D.base encA encB Tb Sb)
    (hleft : ComputableTidilyInO D.left encA encA Tl Sl)
    (hmid : ComputableTidilyInO D.mid (encPair encA encB) (encPair encA encG) Tm Sm)
    (hjoin : ComputableTidilyInO D.join (encPair encG encB) encB Tj Sj)
    (hcb : ∀ a, D.isBase a = true →
      Tt a + St a + Tb a + Sb a + (encA a).length + (encB (D.base a)).length + 1 ≤ cb a)
    (hcn : ∀ a b₁ b₂, D.isBase a = false →
      Tt a + St a + Tl a + Sl a + Tm (a, b₁) + Sm (a, b₁) +
        Tj ((D.mid (a, b₁)).2, b₂) + Sj ((D.mid (a, b₁)).2, b₂) +
        (encA a).length + (encA (D.left a)).length + (encB b₁).length +
        (encA (D.mid (a, b₁)).1).length + (encG (D.mid (a, b₁)).2).length + (encB b₂).length +
        (encB (D.join ((D.mid (a, b₁)).2, b₂))).length + 1 ≤ cn a b₁ b₂)
    (heval : ∀ x, D.Eval cb cn (init x) (F x) (C x)) :
    ComputableTidilyInO F encIn encB (fun x => (encIn x).length + Ti x + Si x + C x)
      (fun x => (encIn x).length + Ti x + Si x + C x) :=
  sorry

end Turing.MultiTapeTM
