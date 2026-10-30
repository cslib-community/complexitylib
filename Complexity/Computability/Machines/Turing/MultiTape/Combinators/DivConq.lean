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

/-! ### The recursion as a stack loop -/

/-- The values of the stack loop: a call on a problem, a returned solution, and the final
solution. -/
abbrev Val (α β : Type) := α ⊕ (β ⊕ β)

/-- The frames of the stack loop: a problem whose first subproblem is being solved, or the data
saved while its second subproblem is solved. -/
abbrev Frame (α γ : Type) := α ⊕ γ

variable (D : DivConq α β γ)

/-- A round on a call: a base problem returns its solution; otherwise the problem is saved and its
first subproblem called. The popped frame is pushed back. -/
@[expose] def roundCall (p : Option (Frame α γ) × α) : List (Frame α γ) × Val α β :=
  if D.isBase p.2 then (p.1.toList, .inr (.inl (D.base p.2)))
  else (.inl p.2 :: p.1.toList, .inl (D.left p.2))

/-- A round on a returned solution: with an empty stack it is final; after a first subproblem the
second is called, saving the data; after a second subproblem the solution is combined. -/
@[expose] def roundRet (p : Option (Frame α γ) × β) : List (Frame α γ) × Val α β :=
  match p.1 with
  | none => ([], .inr (.inr p.2))
  | some (.inl a) => ([.inr (D.mid (a, p.2)).2], .inl (D.mid (a, p.2)).1)
  | some (.inr g) => ([], .inr (.inl (D.join (g, p.2))))

/-- The recursion as a stack loop, halting at a final solution. -/
@[expose] def loop : StackLoop (Val α β) (Frame α γ) where
  halt v := match v with
    | .inr (.inr _) => true
    | _ => false
  round p := match p.2 with
    | .inl a => D.roundCall (p.1, a)
    | .inr (.inl b) => D.roundRet (p.1, b)
    | .inr (.inr b) => (p.1.toList, .inr (.inr b))

omit D in
lemma toList_head?_append_tail (stk : List (Frame α γ)) : stk.head?.toList ++ stk.tail = stk := by
  cases stk <;> rfl

/-- **The trace of an evaluation.** If every round costs at most `R` of its input, and `R` is
bounded on the rounds of base problems and nodes as below, then from a call on `a` the loop
returns the solution of `a`, above an untouched stack, within rounds whose total cost is at most
`A * c` plus `B` times the size of the frame below, plus `B`. -/
theorem eval_trace {cb : α → ℕ} {cn : α → β → β → ℕ} {R : Option (Frame α γ) × Val α β → ℕ}
    {fsize : Option (Frame α γ) → ℕ} {B : ℕ}
    (hbase : ∀ o a, D.isBase a = true → R (o, .inl a) ≤ B * (fsize o + 1) + B * cb a)
    (hcall : ∀ o a b₁ b₂, D.isBase a = false →
      R (o, .inl a) ≤ B * (fsize o + 1) + B * cn a b₁ b₂)
    (hmid : ∀ a b₁ b₂, D.isBase a = false → R (some (.inl a), .inr (.inl b₁)) ≤ B * cn a b₁ b₂)
    (hjoin : ∀ a b₁ b₂, D.isBase a = false →
      R (some (.inr (D.mid (a, b₁)).2), .inr (.inl b₂)) ≤ B * cn a b₁ b₂)
    (hframe : ∀ a b₁ b₂, D.isBase a = false →
      fsize (some (.inl a)) + fsize (some (.inr (D.mid (a, b₁)).2)) + 2 ≤ cn a b₁ b₂)
    {a : α} {b : β} {c : ℕ} (h : D.Eval cb cn a b c) (stk : List (Frame α γ)) :
    ∃ m, (D.loop.step^[m] (.inl a, stk) = (.inr (.inl b), stk)) ∧
      (∀ i < m, D.loop.halt (D.loop.step^[i] (.inl a, stk)).1 = false) ∧
      ∑ i ∈ Finset.range m, R (StackLoop.roundInput (D.loop.step^[i] (.inl a, stk))) ≤
        4 * B * c + B * (fsize stk.head? + 1) := by
  induction h generalizing stk with
  | @base a ha =>
    refine ⟨1, ?_, fun i hi => ?_, ?_⟩
    · simp [StackLoop.step, StackLoop.roundInput, loop, roundCall, ha, toList_head?_append_tail]
    · obtain rfl : i = 0 := by omega
      rfl
    · simp only [Finset.range_one, Finset.sum_singleton, Function.iterate_zero, id_eq]
      have := hbase stk.head? a ha
      simp only [StackLoop.roundInput]
      nlinarith
  | @node a b₁ b₂ c₁ c₂ ha h₁ h₂ ih₁ ih₂ =>
    -- the call round, the first subproblem, the middle round, the second subproblem, the join
    obtain ⟨m₁, hm₁, hh₁, hs₁⟩ := ih₁ (.inl a :: stk)
    obtain ⟨m₂, hm₂, hh₂, hs₂⟩ := ih₂ (.inr (D.mid (a, b₁)).2 :: stk)
    have hcallStep : D.loop.step (.inl a, stk) = (.inl (D.left a), .inl a :: stk) := by
      simp [StackLoop.step, StackLoop.roundInput, loop, roundCall, ha, toList_head?_append_tail]
    have hmidStep : D.loop.step (.inr (.inl b₁), .inl a :: stk) =
        (.inl (D.mid (a, b₁)).1, .inr (D.mid (a, b₁)).2 :: stk) := by
      simp [StackLoop.step, StackLoop.roundInput, loop, roundRet]
    have hjoinStep : D.loop.step (.inr (.inl b₂), .inr (D.mid (a, b₁)).2 :: stk) =
        (.inr (.inl (D.join ((D.mid (a, b₁)).2, b₂))), stk) := by
      simp [StackLoop.step, StackLoop.roundInput, loop, roundRet]
    -- the positions of the phases
    have e₁ : D.loop.step^[m₁ + 1] (.inl a, stk) = (.inr (.inl b₁), .inl a :: stk) := by
      rw [Function.iterate_add_apply, Function.iterate_one, hcallStep, hm₁]
    have e₂ : D.loop.step^[m₂ + 1 + (m₁ + 1)] (.inl a, stk) =
        (.inr (.inl b₂), .inr (D.mid (a, b₁)).2 :: stk) := by
      rw [Function.iterate_add_apply, e₁, Function.iterate_add_apply, Function.iterate_one,
        hmidStep, hm₂]
    refine ⟨1 + (m₂ + 1 + (m₁ + 1)), ?_, fun i hi => ?_, ?_⟩
    · rw [Function.iterate_add_apply, e₂, Function.iterate_one, hjoinStep]
    · -- every round before the end is on a call or a returned solution with a nonempty stack
      rcases Nat.lt_or_ge i (m₁ + 1) with hi₁ | hi₁
      · rcases Nat.eq_zero_or_pos i with rfl | hi₀
        · rfl
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          rw [Function.iterate_add_apply, Function.iterate_one, hcallStep]
          exact hh₁ j (by omega)
      · rcases Nat.lt_or_ge i (m₂ + 1 + (m₁ + 1)) with hi₂ | hi₂
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + (m₁ + 1) := ⟨i - (m₁ + 1), by omega⟩
          rw [Function.iterate_add_apply, e₁]
          rcases Nat.eq_zero_or_pos j with rfl | hj₀
          · rfl
          · obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
            rw [Function.iterate_add_apply, Function.iterate_one, hmidStep]
            exact hh₂ l (by omega)
        · obtain rfl : i = m₂ + 1 + (m₁ + 1) := by omega
          rw [e₂]
          rfl
    · -- the costs of the phases
      have hsplit : ∑ i ∈ Finset.range (1 + (m₂ + 1 + (m₁ + 1))),
            R (StackLoop.roundInput (D.loop.step^[i] (.inl a, stk))) =
          R (stk.head?, .inl a) +
            ∑ i ∈ Finset.range m₁,
              R (StackLoop.roundInput (D.loop.step^[i] (.inl (D.left a), .inl a :: stk))) +
            R (some (.inl a), .inr (.inl b₁)) +
            ∑ i ∈ Finset.range m₂,
              R (StackLoop.roundInput (D.loop.step^[i] (.inl (D.mid (a, b₁)).1,
                .inr (D.mid (a, b₁)).2 :: stk))) +
            R (some (.inr (D.mid (a, b₁)).2), .inr (.inl b₂)) := by
        rw [show 1 + (m₂ + 1 + (m₁ + 1)) = 1 + m₁ + 1 + m₂ + 1 by omega, Finset.sum_range_succ,
          Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_add, Finset.sum_range_one]
        simp only [Function.iterate_zero, id_eq, StackLoop.roundInput]
        have hA : ∀ x, D.loop.step^[1 + x] (.inl a, stk) =
            D.loop.step^[x] (.inl (D.left a), .inl a :: stk) := fun x => by
          rw [add_comm, Function.iterate_add_apply, Function.iterate_one, hcallStep]
        have hB : ∀ x, D.loop.step^[1 + m₁ + 1 + x] (.inl a, stk) =
            D.loop.step^[x] (.inl (D.mid (a, b₁)).1, .inr (D.mid (a, b₁)).2 :: stk) :=
          fun x => by
            rw [show 1 + m₁ + 1 + x = x + 1 + (m₁ + 1) by omega, Function.iterate_add_apply, e₁,
              Function.iterate_add_apply, Function.iterate_one, hmidStep]
        simp only [hA, hB, hm₁, hm₂, List.head?_cons]
      rw [hsplit]
      have h₀ := hcall stk.head? a b₁ b₂ ha
      have h₃ := hmid a b₁ b₂ ha
      have h₄ := hjoin a b₁ b₂ ha
      have h₅ := hframe a b₁ b₂ ha
      simp only [List.head?_cons] at hs₁ hs₂
      nlinarith

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
