/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.StackLoop
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases

/-!
# Divide and conquer

A divide-and-conquer recursion (`Turing.MultiTapeTM.DivConq`) solves a base problem directly and
otherwise solves a first subproblem, derives a second subproblem and some saved data from the
problem and the first solution, solves the second subproblem, and combines the saved data with the
second solution. Its evaluation with a cost is the inductive relation
`Turing.MultiTapeTM.DivConq.Eval`: a node costs its two subproblems plus a cost of its own.

If the parts are computable, the solution is computable within the cost of the evaluation, when
the cost of every node covers the costs of its parts and the lengths of the words it touches
(`Turing.MultiTapeTM.ComputableInO.divConq`). The machine runs the recursion as a
`Turing.MultiTapeTM.StackLoop`, keeping the pending problems and saved data on a stack, so a node
does not pay for the frames of its ancestors.

## Main definitions

* `Turing.MultiTapeTM.DivConq`: the parts of a divide-and-conquer recursion.
* `Turing.MultiTapeTM.DivConq.Eval`: evaluation with a cost.

## Main results

* `Turing.MultiTapeTM.ComputableInO.divConq`: divide and conquer within the cost of the
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

namespace Eval

variable {D : DivConq α β γ} {cb : α → ℕ} {cn : α → β → β → ℕ}

/-- Scaling the costs of base problems and nodes scales the cost of an evaluation. -/
lemma scale (k : ℕ) {a : α} {b : β} {c : ℕ} (h : D.Eval cb cn a b c) :
    D.Eval (fun a => k * cb a) (fun a b₁ b₂ => k * cn a b₁ b₂) a b (k * c) := by
  induction h with
  | base ha => exact .base ha
  | node ha _ _ ih₁ ih₂ => rw [Nat.mul_add, Nat.mul_add]; exact .node ha ih₁ ih₂

/-- The problem and its solution are within the cost of an evaluation, when the cost of every base
problem and node covers them. -/
lemma length_le {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    (hb : ∀ a, D.isBase a = true → (encA a).length + (encB (D.base a)).length ≤ cb a)
    (hn : ∀ a b₁ b₂, D.isBase a = false →
      (encA a).length + (encB (D.join ((D.mid (a, b₁)).2, b₂))).length ≤ cn a b₁ b₂)
    {a : α} {b : β} {c : ℕ} (h : D.Eval cb cn a b c) : (encA a).length + (encB b).length ≤ c := by
  induction h with
  | base ha => exact hb _ ha
  | @node a b₁ b₂ c₁ c₂ ha _ _ _ _ => have := hn a b₁ b₂ ha; omega

end Eval

/-! ### The recursion as a stack loop -/

/-- The values of the stack loop: a call on a problem, a returned solution, and the final
solution. -/
private abbrev Val (α β : Type) := α ⊕ (β ⊕ β)

/-- The frames of the stack loop: a problem whose first subproblem is being solved, or the data
saved while its second subproblem is solved. -/
private abbrev Frame (α γ : Type) := α ⊕ γ

variable (D : DivConq α β γ)

/-- A round on a call: a base problem returns its solution; otherwise the problem is saved and its
first subproblem called. The popped frame is pushed back. -/
private def roundCall (p : Option (Frame α γ) × α) : List (Frame α γ) × Val α β :=
  if D.isBase p.2 then (p.1.toList, .inr (.inl (D.base p.2)))
  else (.inl p.2 :: p.1.toList, .inl (D.left p.2))

/-- A round on a returned solution: with an empty stack it is final; after a first subproblem the
second is called, saving the data; after a second subproblem the solution is combined. -/
private def roundRet (p : Option (Frame α γ) × β) : List (Frame α γ) × Val α β :=
  match p.1 with
  | none => ([], .inr (.inr p.2))
  | some (.inl a) => ([.inr (D.mid (a, p.2)).2], .inl (D.mid (a, p.2)).1)
  | some (.inr g) => ([], .inr (.inl (D.join (g, p.2))))

/-- The recursion as a stack loop, halting at a final solution. -/
private def loop : StackLoop (Val α β) (Frame α γ) where
  halt v := match v with
    | .inr (.inr _) => true
    | _ => false
  round p := match p.2 with
    | .inl a => D.roundCall (p.1, a)
    | .inr (.inl b) => D.roundRet (p.1, b)
    | .inr (.inr b) => (p.1.toList, .inr (.inr b))

omit D in
private lemma toList_head?_append_tail (stk : List (Frame α γ)) :
    stk.head?.toList ++ stk.tail = stk := by
  cases stk <;> rfl

/-- **The trace of an evaluation.** If every round costs at most `R` of its input, and `R` is
bounded on the rounds of base problems and nodes as below, then from a call on `a` the loop
returns the solution of `a`, above an untouched stack, within rounds whose total cost is at most
`4 * B * c` plus `B` times one more than the size of the top frame below. -/
private theorem eval_trace {cb : α → ℕ} {cn : α → β → β → ℕ} {R : Option (Frame α γ) × Val α β → ℕ}
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

/-! ### Certificates for the rounds -/

namespace DivConq

open ComputableTidilyInO

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encG : γ ↪ List Bool}

/-- The encoding of the values of the loop. -/
private abbrev encVal (encA : α ↪ List Bool) (encB : β ↪ List Bool) : Val α β ↪ List Bool :=
  encSum encA (encSum encB encB)

/-- The encoding of the frames of the loop. -/
private abbrev encFrame (encA : α ↪ List Bool) (encG : γ ↪ List Bool) : Frame α γ ↪ List Bool :=
  encSum encA encG

/-- `Option.toList`, in linear time. -/
private lemma toList_inO {δ : Type} {enc : δ ↪ List Bool} :
    ComputableTidilyInO (Option.toList (α := δ)) (encOption enc) (encList enc)
      (fun o => (encOption enc o).length) (fun o => (encOption enc o).length) := by
  have htail : ComputableTidilyInO List.tail encBits encBits (fun w => w.length)
      (fun w => w.length) :=
    of_linear (.of_tail (f := List.tail) (encIn := encBits) (encOut := encBits) fun _ => rfl)
  have hframe : ComputableTidilyInO frame encBits encBits (fun w => w.length)
      (fun w => w.length) :=
    of_linear (.of_frame (f := frame) (encIn := encBits) (encOut := encBits) fun _ => rfl)
  have hft : ComputableTidilyInO (fun w : List Bool => frame w.tail) encBits encBits
      (fun w => w.length) (fun w => w.length) :=
    (hframe.comp htail).mono 2 (fun w => by simp; omega) (fun w => by simp; omega)
  have hw : ComputableTidilyInO (fun w : List Bool => if w.isEmpty then [] else frame w.tail)
      encBits encBits (fun w => w.length) (fun w => w.length) :=
    ((of_linear (.of_isEmpty (f := List.isEmpty) (encIn := encBits) fun _ => rfl)).ite
      (const (encMid := encBits) []) hft).mono 2 (fun w => by split_ifs <;> simp <;>
        omega) (fun w => by split_ifs <;> simp <;> omega)
  refine (hw.comp (of_linear (.of_eq (f := fun o : Option δ => encOption enc o)
    (encIn := encOption enc) (encMid := encBits) fun _ => rfl))).of_enc_eq (fun o => ?_) |>.mono
      2 (fun o => ?_) (fun o => ?_)
  · cases o <;> simp [encBits]
  all_goals omega

/-- The sums of the costs of a run of `m + 1` rounds followed by a halting test, against a bound
on the first `m` rounds. -/
private lemma sums_le {A B R : ℕ → ℕ} {m X : ℕ} (h : ∀ i < m, A i + B i ≤ R i) :
    X + ∑ i ∈ Finset.range (m + 1 + 1), A i + ∑ i ∈ Finset.range (m + 1), B i ≤
      X + (∑ i ∈ Finset.range m, R i + A m + A (m + 1) + B m) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have := Finset.sum_le_sum (s := Finset.range m) fun i hi => h i (Finset.mem_range.mp hi)
  rw [Finset.sum_add_distrib] at this
  omega

private lemma length_encList_toList_le {δ : Type} (enc : δ ↪ List Bool) (o : Option δ) :
    (encList enc o.toList).length ≤ 2 * (encOption enc o).length := by
  cases o <;> simp [length_frame]

variable (D : DivConq α β γ) {Tt St Tb Sb Tl Sl : α → ℕ} {Tm Sm : α × β → ℕ}
  {Tj Sj : γ × β → ℕ}

/-- The swap of the components of a pair, in linear time. -/
private lemma swap_inO {σ τ : Type} {encS : σ ↪ List Bool} {encT : τ ↪ List Bool} :
    ComputableTidilyInO (fun p : σ × τ => (p.2, p.1)) (encPair encS encT) (encPair encT encS)
      (fun p => (encPair encS encT p).length) (fun p => (encPair encS encT p).length) :=
  ((snd encS encT).prod (fst encS encT)).mono 2 (fun _ => by omega) (fun _ => by omega)

/-- A call round, within the costs of its parts. -/
private lemma roundCall_inO (hisBase : ComputableTidilyInO D.isBase encA encBool Tt St)
    (hbase : ComputableTidilyInO D.base encA encB Tb Sb)
    (hleft : ComputableTidilyInO D.left encA encA Tl Sl) :
    ComputableTidilyInO D.roundCall (encPair (encOption (encFrame encA encG)) encA)
      (encPair (encList (encFrame encA encG)) (encVal encA encB))
      (fun p => (encPair (encOption (encFrame encA encG)) encA p).length + Tt p.2 + St p.2 +
        if D.isBase p.2 then Tb p.2 + Sb p.2 + (encB (D.base p.2)).length
        else Tl p.2 + Sl p.2 + (encA (D.left p.2)).length)
      (fun p => (encPair (encOption (encFrame encA encG)) encA p).length + Tt p.2 + St p.2 +
        if D.isBase p.2 then Tb p.2 + Sb p.2 + (encB (D.base p.2)).length
        else Tl p.2 + Sl p.2 + (encA (D.left p.2)).length) := by
  have hfst := fst (encOption (encFrame encA encG)) encA
  have hsnd := snd (encOption (encFrame encA encG)) encA
  have hc := hisBase.comp hsnd
  have hl := (toList_inO (enc := encFrame encA encG)).comp hfst
  have hb := (ComputableInO.inr encA (encSum encB encB)).tidy.comp
    ((ComputableInO.inl encB encB).tidy.comp (hbase.comp hsnd))
  have hcons := (ComputableTidilyInDegree.cons (encFrame encA encG)).inO_one.comp
    (((ComputableInO.inl encA encG).tidy.comp hsnd).prod hl)
  have hlf := (ComputableInO.inl encA (encSum encB encB)).tidy.comp (hleft.comp hsnd)
  refine (hc.ite (hl.prod hb) (hcons.prod hlf)).mono 8 (fun p => ?_) (fun p => ?_)
  all_goals
    obtain ⟨o, a⟩ := p
    have h₁ := length_encList_toList_le (encFrame encA encG) o
    simp only [Function.comp_apply, length_encPair, encSum_inl, List.length_cons] at *
    split_ifs <;> nlinarith

/-- `fun b => ([], inr (inr b))`, in linear time. -/
private lemma final_inO :
    ComputableTidilyInO (fun b : β => (([] : List (Frame α γ)), (.inr (.inr b) : Val α β))) encB
      (encPair (encList (encFrame encA encG)) (encVal encA encB)) (fun b => (encB b).length)
      (fun b => (encB b).length) :=
  ((const (encMid := encList (encFrame encA encG)) []).prod
    ((ComputableInO.inr encA (encSum encB encB)).tidy.comp
      (ComputableInO.inr encB encB).tidy)).mono 4 (fun b => by simp; omega)
    (fun b => by simp; omega)

/-- A round on a returned solution, with the components swapped, within the costs of its
parts. -/
private lemma retSwap_inO
    (hmid : ComputableTidilyInO D.mid (encPair encA encB) (encPair encA encG) Tm Sm)
    (hjoin : ComputableTidilyInO D.join (encPair encG encB) encB Tj Sj) :
    ComputableTidilyInO (fun q : β × Option (Frame α γ) => q.2.elim
        (([] : List (Frame α γ)), (.inr (.inr q.1) : Val α β))
        (fun x => x.elim (fun a => ([.inr (D.mid (a, q.1)).2], .inl (D.mid (a, q.1)).1))
          (fun g => ([], .inr (.inl (D.join (g, q.1)))))))
      (encPair encB (encOption (encFrame encA encG)))
      (encPair (encList (encFrame encA encG)) (encVal encA encB))
      (fun q => (encPair encB (encOption (encFrame encA encG)) q).length + q.2.elim 0
        (fun x => x.elim
          (fun a => Tm (a, q.1) + Sm (a, q.1) + (encPair encA encG (D.mid (a, q.1))).length)
          (fun g => Tj (g, q.1) + Sj (g, q.1) + (encB (D.join (g, q.1))).length)))
      (fun q => (encPair encB (encOption (encFrame encA encG)) q).length + q.2.elim 0
        (fun x => x.elim
          (fun a => Tm (a, q.1) + Sm (a, q.1) + (encPair encA encG (D.mid (a, q.1))).length)
          (fun g => Tj (g, q.1) + Sj (g, q.1) + (encB (D.join (g, q.1))).length))) := by
  -- the middle: the second subproblem is called, the saved data pushed
  have hm := hmid.comp (swap_inO (encS := encB) (encT := encA))
  have hpush := (ComputableTidilyInDegree.cons (encFrame encA encG)).inO_one.comp
    (((ComputableInO.inr encA encG).tidy.comp ((snd encA encG).comp hm)).prod
      ((const (encMid := encList (encFrame encA encG)) []).comp hm))
  have hcall := (ComputableInO.inl encA (encSum encB encB)).tidy.comp ((fst encA encG).comp hm)
  have hM := hpush.prod hcall
  -- the combination
  have hj := hjoin.comp (swap_inO (encS := encB) (encT := encG))
  have hJ := (const (encMid := encList (encFrame encA encG)) []).prod
    ((ComputableInO.inr encA (encSum encB encB)).tidy.comp
      ((ComputableInO.inl encB encB).tidy.comp hj))
  have hx := ComputableInO.sumElimSnd hM.computableInO hJ.computableInO
  have h := ComputableInO.optionElimSnd (final_inO (encA := encA) (encG := encG)).computableInO hx
  refine h.tidy.mono 16 (fun q => ?_) (fun q => ?_)
  all_goals
    obtain ⟨b, _ | _ | _⟩ := q <;>
    simp only [Function.comp_apply, length_encPair, encSum_inl, encSum_inr, List.length_cons,
      Option.elim_none, Option.elim_some, Sum.elim_inl, Sum.elim_inr, encOption_some,
      encList_nil, List.length_nil] at * <;>
    nlinarith

/-- A round, within the costs of the parts of the recursion it runs. -/
private lemma round_inO (hisBase : ComputableTidilyInO D.isBase encA encBool Tt St)
    (hbase : ComputableTidilyInO D.base encA encB Tb Sb)
    (hleft : ComputableTidilyInO D.left encA encA Tl Sl)
    (hmid : ComputableTidilyInO D.mid (encPair encA encB) (encPair encA encG) Tm Sm)
    (hjoin : ComputableTidilyInO D.join (encPair encG encB) encB Tj Sj) :
    ComputableTidilyInO D.loop.round
      (encPair (encOption (encFrame encA encG)) (encVal encA encB))
      (encPair (encList (encFrame encA encG)) (encVal encA encB))
      (fun p => (encPair (encOption (encFrame encA encG)) (encVal encA encB) p).length + p.2.elim
        (fun a => Tt a + St a + if D.isBase a then Tb a + Sb a + (encB (D.base a)).length
          else Tl a + Sl a + (encA (D.left a)).length)
        (fun s => s.elim (fun b => p.1.elim 0 (fun x => x.elim
          (fun a => Tm (a, b) + Sm (a, b) + (encPair encA encG (D.mid (a, b))).length)
          (fun g => Tj (g, b) + Sj (g, b) + (encB (D.join (g, b))).length))) (fun _ => 0)))
      (fun p => (encPair (encOption (encFrame encA encG)) (encVal encA encB) p).length + p.2.elim
        (fun a => Tt a + St a + if D.isBase a then Tb a + Sb a + (encB (D.base a)).length
          else Tl a + Sl a + (encA (D.left a)).length)
        (fun s => s.elim (fun b => p.1.elim 0 (fun x => x.elim
          (fun a => Tm (a, b) + Sm (a, b) + (encPair encA encG (D.mid (a, b))).length)
          (fun g => Tj (g, b) + Sj (g, b) + (encB (D.join (g, b))).length))) (fun _ => 0))) := by
  have hCall := D.roundCall_inO (encG := encG) hisBase hbase hleft
  have hRet := (D.retSwap_inO hmid hjoin).comp
    (swap_inO (encS := encOption (encFrame encA encG)) (encT := encB))
  have hFin := ((toList_inO (enc := encFrame encA encG)).comp
    (fst (encOption (encFrame encA encG)) encB)).prod
    ((ComputableInO.inr encA (encSum encB encB)).tidy.comp
      ((ComputableInO.inr encB encB).tidy.comp (snd (encOption (encFrame encA encG)) encB)))
  have hS := ComputableInO.sumElimSnd hRet.computableInO hFin.computableInO
  have hR := ComputableInO.sumElimSnd hCall.computableInO hS
  refine (hR.tidy.of_enc_eq fun p => ?_).mono 8 (fun p => ?_) (fun p => ?_)
  · obtain ⟨o, a | b | b⟩ := p
    · rfl
    · rcases o with _ | a | g <;> rfl
    · rfl
  all_goals
    obtain ⟨o, a | b | b⟩ := p
    · simp only [Sum.elim_inl, length_encPair, encSum_inl, List.length_cons]
      split_ifs <;> omega
    · rcases o with _ | a | g <;>
      simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr, Option.elim_none,
        Option.elim_some, length_encPair, encSum_inl, encSum_inr, List.length_cons,
        encOption_some] <;> omega
    · have := length_encList_toList_le (encFrame encA encG) o
      simp only [Function.comp_apply, Sum.elim_inr, length_encPair, encSum_inr,
        List.length_cons] at *
      omega

/-- The halting test of the loop, in linear time. -/
private lemma halt_inO : ComputableTidilyInO D.loop.halt (encVal encA encB) encBool
    (fun v => (encVal encA encB v).length) (fun v => (encVal encA encB v).length) := by
  have hw : ComputableTidilyInO (fun w : List Bool => (w.headD false, w.tail.headD false))
      encBits (encPair encBool encBool) (fun w => w.length) (fun w => w.length) :=
    ((ComputableTidilyInDegree.headD (enc₁ := encBool) (enc := encBits) false).inO_one.prod
      ((ComputableTidilyInDegree.headD (enc₁ := encBool) (enc := encBits) false).inO_one.comp
        (of_linear (.of_tail (f := List.tail) (encIn := encBits) (encOut := encBits)
          fun _ => rfl)))).mono 3 (fun w => by simp [encBits]; omega)
      (fun w => by simp [encBits]; omega)
  refine (((ComputableTidilyInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) (fun p : Bool × Bool => p.1 && p.2)).inO_one.comp hw).comp
    (of_linear (.of_eq (f := fun v : Val α β => encVal encA encB v) (encIn := encVal encA encB)
      (encMid := encBits) fun _ => rfl))).of_enc_eq (fun v => ?_) |>.mono 4 (fun v => ?_)
      (fun v => ?_)
  · rcases v with a | b | b <;> rfl
  all_goals simp; omega

end DivConq

/-- **Divide and conquer.** If the parts of a divide-and-conquer recursion are computable and every
input `x` is solved with `F x` at cost `C x`, then `F` is computable within the cost of the
evaluation plus the initialization. The cost of a base problem must cover its test, its solution
and the lengths of the problem and its solution; the cost of a node must cover its test, the first
subproblem, the middle and the combination, and the lengths of all the values they read and
write. -/
theorem ComputableInO.divConq {δ α β γ : Type} {encIn : δ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encG : γ ↪ List Bool} (D : DivConq α β γ)
    {init : δ → α} {F : δ → β} {C : δ → ℕ} {cb : α → ℕ} {cn : α → β → β → ℕ}
    {Ti Si : δ → ℕ} {Tt St Tb Sb Tl Sl : α → ℕ} {Tm Sm : α × β → ℕ} {Tj Sj : γ × β → ℕ}
    (hinit : ComputableInO init encIn encA Ti Si)
    (hisBase : ComputableInO D.isBase encA encBool Tt St)
    (hbase : ComputableInO D.base encA encB Tb Sb)
    (hleft : ComputableInO D.left encA encA Tl Sl)
    (hmid : ComputableInO D.mid (encPair encA encB) (encPair encA encG) Tm Sm)
    (hjoin : ComputableInO D.join (encPair encG encB) encB Tj Sj)
    (hcb : ∀ a, D.isBase a = true →
      Tt a + St a + Tb a + Sb a + (encA a).length + (encB (D.base a)).length + 1 ≤ cb a)
    (hcn : ∀ a b₁ b₂, D.isBase a = false →
      Tt a + St a + Tl a + Sl a + Tm (a, b₁) + Sm (a, b₁) +
        Tj ((D.mid (a, b₁)).2, b₂) + Sj ((D.mid (a, b₁)).2, b₂) +
        (encA a).length + (encA (D.left a)).length + (encB b₁).length +
        (encA (D.mid (a, b₁)).1).length + (encG (D.mid (a, b₁)).2).length + (encB b₂).length +
        (encB (D.join ((D.mid (a, b₁)).2, b₂))).length + 1 ≤ cn a b₁ b₂)
    (heval : ∀ x, D.Eval cb cn (init x) (F x) (C x)) :
    ComputableInO F encIn encB (fun x => (encIn x).length + Ti x + Si x + C x)
      (fun x => (encIn x).length + Ti x + Si x + C x) := by
  classical
  -- the certificates of the loop
  have hR := D.round_inO (encG := encG) hisBase.tidy hbase.tidy hleft.tidy hmid.tidy hjoin.tidy
  have hH := D.halt_inO (encA := encA) (encB := encB)
  have hI := (ComputableInO.inl encA (encSum encB encB)).tidy.comp hinit.tidy
  set encF := DivConq.encFrame encA encG with hencF
  set encV := DivConq.encVal encA encB with hencV
  -- the cost of a round
  let RB : Option (DivConq.Frame α γ) × DivConq.Val α β → ℕ := fun p =>
    (encPair (encOption encF) encV p).length + p.2.elim
      (fun a => Tt a + St a + if D.isBase a then Tb a + Sb a + (encB (D.base a)).length
        else Tl a + Sl a + (encA (D.left a)).length)
      (fun s => s.elim (fun b => p.1.elim 0 (fun x => x.elim
        (fun a => Tm (a, b) + Sm (a, b) + (encPair encA encG (D.mid (a, b))).length)
        (fun g => Tj (g, b) + Sj (g, b) + (encB (D.join (g, b))).length))) (fun _ => 0))
  let R : Option (DivConq.Frame α γ) × DivConq.Val α β → ℕ := fun p =>
    (encV p.2).length + (encV p.2).length + (encV p.2).length + (RB p + RB p +
      (encPair (encOption encF) encV p).length +
      (encPair (encList encF) encV (D.loop.round p)).length)
  let fsize : Option (DivConq.Frame α γ) → ℕ := fun o => (encOption encF o).length
  -- the bounds of the rounds of base problems and nodes
  have hb' : ∀ o a, D.isBase a = true →
      R (o, .inl a) ≤ 64 * (fsize o + 1) + 64 * (6 * cb a) := by
    intro o a ha
    have h₁ := hcb a ha
    have h₂ := DivConq.length_encList_toList_le encF o
    simp only [R, RB, fsize, DivConq.loop, DivConq.roundCall, ha, Sum.elim_inl, ite_true,
      length_encPair, hencV, hencF, encSum_inl, encSum_inr, List.length_cons] at h₂ ⊢
    omega
  have hc' : ∀ o a b₁ b₂, D.isBase a = false →
      R (o, .inl a) ≤ 64 * (fsize o + 1) + 64 * (6 * cn a b₁ b₂) := by
    intro o a b₁ b₂ ha
    have h₁ := hcn a b₁ b₂ ha
    have h₂ := DivConq.length_encList_toList_le encF o
    simp only [R, RB, fsize, DivConq.loop, DivConq.roundCall, ha, Sum.elim_inl,
      Bool.false_eq_true, ite_false, length_encPair, hencV, hencF, encSum_inl,
      List.length_cons, encList_cons, List.length_append, length_frame] at h₂ ⊢
    omega
  have hm' : ∀ a b₁ b₂, D.isBase a = false →
      R (some (.inl a), .inr (.inl b₁)) ≤ 64 * (6 * cn a b₁ b₂) := by
    intro a b₁ b₂ ha
    have h₁ := hcn a b₁ b₂ ha
    simp only [R, RB, DivConq.loop, DivConq.roundRet, Sum.elim_inl, Sum.elim_inr,
      Option.elim_some, length_encPair, hencV, hencF, encSum_inl, encSum_inr, List.length_cons,
      encOption_some, encList_cons, encList_nil, List.append_nil, length_frame]
    omega
  have hj' : ∀ a b₁ b₂, D.isBase a = false →
      R (some (.inr (D.mid (a, b₁)).2), .inr (.inl b₂)) ≤ 64 * (6 * cn a b₁ b₂) := by
    intro a b₁ b₂ ha
    have h₁ := hcn a b₁ b₂ ha
    simp only [R, RB, DivConq.loop, DivConq.roundRet, Sum.elim_inl, Sum.elim_inr,
      Option.elim_some, length_encPair, hencV, hencF, encSum_inl, encSum_inr, List.length_cons,
      encOption_some, encList_nil, List.length_nil]
    omega
  have hf' : ∀ a b₁ b₂, D.isBase a = false →
      fsize (some (.inl a)) + fsize (some (.inr (D.mid (a, b₁)).2)) + 2 ≤ 6 * cn a b₁ b₂ := by
    intro a b₁ b₂ ha
    have h₁ := hcn a b₁ b₂ ha
    simp only [fsize, hencF, encOption_some, encSum_inl, encSum_inr, List.length_cons]
    omega
  -- the trace of every input
  have htrace := fun x => D.eval_trace hb' hc' hm' hj' hf' ((heval x).scale 6) []
  choose m hm hh hs using htrace
  have hfinal : ∀ x, D.loop.step^[m x + 1] (.inl (init x), []) = (.inr (.inr (F x)), []) :=
    fun x => by rw [Function.iterate_succ_apply', hm x]; rfl
  have hlen := fun x => DivConq.Eval.length_le (encA := encA) (encB := encB)
    (fun a ha => by have := hcb a ha; omega)
    (fun a b₁ b₂ ha => by have := hcn a b₁ b₂ ha; omega) (heval x)
  have hSL := ComputableInO.stackLoop D.loop (fun x => m x + 1) hI.computableInO
    hH.computableInO hR.computableInO
    (fun x i hi => by
      rcases Nat.lt_or_ge i (m x) with hi' | hi'
      · exact hh x i hi'
      · obtain rfl : i = m x := by omega
        simp only [Function.comp_apply, hm x]; rfl)
    (fun x => by simp only [Function.comp_apply, hfinal x]; rfl)
    (fun x => by simp only [Function.comp_apply, hfinal x])
  -- the solution is the final value without its two tags
  have hdrop : ComputableTidilyInO (fun v : DivConq.Val α β => (encV v).drop 2) encV encBits
      (fun v => (encV v).length) (fun v => (encV v).length) := by
    have htail : ComputableTidilyInO List.tail encBits encBits (fun w => w.length)
        (fun w => w.length) :=
      ComputableTidilyInO.of_linear (ComputableTidilyInLinearTimeAndSpace.of_tail
        (f := List.tail) (encIn := encBits) (encOut := encBits) fun _ => rfl)
    refine ((htail.comp htail).comp (ComputableTidilyInO.of_linear
      (ComputableTidilyInLinearTimeAndSpace.of_eq (f := fun v => encV v) (encIn := encV)
        (encMid := encBits) fun _ => rfl))).of_enc_eq (fun v => ?_) |>.mono 3 (fun v => ?_)
        (fun v => ?_)
    · simp only [Function.comp_apply, encBits, Function.Embedding.refl_apply]
      generalize encV v = w
      rcases w with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
    all_goals simp; omega
  refine ((hdrop.comp hSL.tidy).of_enc_eq (g := F) fun x => ?_).computableInO.mono 4000
    (fun x => ?_) (fun x => ?_)
  · simp only [Function.comp_apply, hfinal, hencV, encSum_inr, encBits,
      Function.Embedding.refl_apply, List.drop_succ_cons, List.drop_zero]
  all_goals
    have hsx := hs x
    have hlx := hlen x
    simp only [Function.comp_apply]
    refine le_trans (Nat.add_le_add_right (DivConq.sums_le (R := fun i => R
      (StackLoop.roundInput (D.loop.step^[i] (.inl (init x), [])))) ?_) _) ?_
    · intro i _
      exact le_of_eq rfl
    have hround : D.loop.round (none, .inr (.inl (F x))) = ([], .inr (.inr (F x))) := rfl
    simp only [hm x, hfinal x, StackLoop.roundInput, List.head?_nil, hround] at hsx ⊢
    simp only [hencV, hencF, Option.elim_none, Sum.elim_inr, Sum.elim_inl, length_encPair,
      encSum_inr, encSum_inl, List.length_cons, encOption_none, encList_nil, List.length_nil,
      fsize] at hsx ⊢
    omega

end Turing.MultiTapeTM
