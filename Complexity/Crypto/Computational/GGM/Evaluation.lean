/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime

/-!
# Evaluating the GGM tree

Starting from a secret root label, follow the query bits down a binary tree. Each expansion
provides two labels of the current seed width. The evaluator is an ordinary word fold, and its
polynomial-time certificate comes from the fold compiler.

Extra generator output is discarded. In particular, a generator of length `2 * n + 1` supplies
both `n`-bit children even at `n = 0`, where the result is the empty word.

This module proves evaluation and size properties. Pseudorandomness requires the adaptive
oracle hybrid argument in addition to these facts.

The functional construction is ported from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`; efficiency uses the plain machine calculus.

## Main definitions

* `Cslib.Crypto.GGM.eval`: evaluate a binary query by folding child selection over its bits.

## Main results

* `Cslib.Crypto.GGM.length_eval`: evaluation preserves the seed width for full expansions.
* `Cslib.Crypto.GGM.computableInPolyTime_eval`: a uniform machine certificate without
  a cryptographic security hypothesis or an output-length hypothesis on the generator.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.2.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Turing.MultiTapeTM

/-- Select one of the two consecutive child labels, discarding any surplus expansion bits. -/
def selectChild (width : ℕ) (expansion : List Bool) (bit : Bool) : List Bool :=
  if bit then (expansion.drop width).take width else expansion.take width

/-- Each child fits in the declared width, even when the expansion is short. -/
theorem length_selectChild_le (width : ℕ) (expansion : List Bool) (bit : Bool) :
    (selectChild width expansion bit).length ≤ width := by
  cases bit <;> simp [selectChild]

/-- Child selection inspects only the first two labels. -/
@[simp] theorem selectChild_take (width : ℕ) (expansion : List Bool) (bit : Bool) :
    selectChild width (expansion.take (2 * width)) bit = selectChild width expansion bit := by
  cases bit <;>
    simp [selectChild, List.drop_take, List.take_take,
      show 2 * width - width = width by lia, Nat.min_eq_left (by lia : width ≤ 2 * width)]

/-- Expand a node and select the child indicated by one query bit. -/
def child (generator : List Bool → List Bool) (seed : List Bool) (bit : Bool) : List Bool :=
  selectChild seed.length (generator seed) bit

/-- Follow a query from a root seed, reading its bits from left to right. -/
def eval (generator : List Bool → List Bool) (seed query : List Bool) : List Bool :=
  query.foldl (child generator) seed

/-- Tree evaluation uses only the first two labels of every generator output. -/
@[simp] theorem eval_truncate (generator : List Bool → List Bool) :
    eval (fun seed => (generator seed).take (2 * seed.length)) = eval generator := by
  funext seed query
  unfold eval child
  simp only [selectChild_take]

@[simp] theorem eval_nil (generator : List Bool → List Bool) (seed : List Bool) :
    eval generator seed [] = seed := rfl

@[simp] theorem eval_cons (generator : List Bool → List Bool) (seed : List Bool) (bit : Bool)
    (query : List Bool) :
    eval generator seed (bit :: query) = eval generator (child generator seed bit) query := rfl

/-- A shared query prefix leads to the same intermediate node. -/
theorem eval_append (generator : List Bool → List Bool) (seed path suffix : List Bool) :
    eval generator seed (path ++ suffix) = eval generator (eval generator seed path) suffix :=
  List.foldl_append

/-- Expose the next edge of a nonempty suffix using its position in the original query. -/
theorem eval_drop_succ (generator : List Bool → List Bool) (seed query : List Bool) (depth : ℕ)
    (hdepth : depth < query.length) :
    eval generator seed (query.drop depth) =
      eval generator (child generator seed (query[depth]?.getD false))
        (query.drop (depth + 1)) := by
  rw [List.drop_eq_getElem_cons hdepth]
  simp only [eval_cons, List.getElem?_eq_getElem hdepth, Option.getD_some]

/-- Truncation bounds intermediate labels even for an arbitrary generator. -/
theorem length_child_le (generator : List Bool → List Bool) (seed : List Bool) (bit : Bool) :
    (child generator seed bit).length ≤ seed.length :=
  length_selectChild_le _ _ _

/-- A generator providing two full labels preserves the seed width on each edge. -/
theorem length_child {generator : List Bool → List Bool}
    (hlength : ∀ seed, 2 * seed.length ≤ (generator seed).length) (seed : List Bool) (bit : Bool) :
    (child generator seed bit).length = seed.length := by
  have := hlength seed
  cases bit <;>
    simp only [child, selectChild, Bool.false_eq_true, ↓reduceIte,
      List.length_take, List.length_drop]
  all_goals lia

/-- All labels encountered by tree evaluation fit in the original seed width. -/
theorem length_eval_le (generator : List Bool → List Bool) (seed query : List Bool) :
    (eval generator seed query).length ≤ seed.length := by
  induction query generalizing seed with
  | nil => simp
  | cons bit query ih => exact (ih _).trans (length_child_le generator seed bit)

/-- Tree evaluation preserves the seed width at every depth when both children are full length. -/
theorem length_eval {generator : List Bool → List Bool}
    (hlength : ∀ seed, 2 * seed.length ≤ (generator seed).length) (seed query : List Bool) :
    (eval generator seed query).length = seed.length := by
  induction query generalizing seed with
  | nil => simp
  | cons bit query ih => rw [eval_cons, ih, length_child hlength]

/-- Select a child using a computed unary width and ordinary bit-string slicing. -/
@[fun_prop]
theorem computableInPolyTime_selectChild {α : Type} {input : α ↪ List Bool}
    {width : α → ℕ} {expansion : α → List Bool} {bit : α → Bool}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hexpansion : ComputableInPolyTime expansion input encBits)
    (hbit : ComputableInPolyTime bit input encBool) :
    ComputableInPolyTime (fun a => selectChild (width a) (expansion a) (bit a))
      input encBits := by
  unfold selectChild
  exact hbit.ite
    (ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsDropWithInput hexpansion hwidth) hwidth)
    (ComputableInPolyTime.bitsTakeWithInput hexpansion hwidth)

/-- Computing one child invokes the certified generator and slices its output. -/
@[fun_prop]
theorem computableInPolyTime_child {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits) :
    ComputableInPolyTime (fun pair : List Bool × Bool => child generator pair.1 pair.2)
      (encPair encBits encBool) encBits := by
  fun_prop [child]

/-- The GGM evaluator is polynomial time whenever its generator is. Its fold has no state growth,
so this certificate needs no security or output-length assumption. -/
@[fun_prop]
theorem computableInPolyTime_eval {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits) :
    ComputableInPolyTime (fun pair : List Bool × List Bool => eval generator pair.1 pair.2)
      (encPair encBits encBits) encBits := by
  unfold eval
  exact ComputableInPolyTime.foldl' (encA := encBool) (encL := encBits) (encB := encBits)
    (ComputableInPolyTime.snd encBits encBits)
    (ComputableInPolyTime.fst encBits encBits)
    (computableInPolyTime_child hgenerator)
    (B := fun pair : List Bool × List Bool => (encPair encBits encBits pair).length)
    PolyBounded.self fun pair i _ => by
      simp only [encBits_apply, length_encPair]
      exact (length_eval_le generator pair.1 (pair.2.take i)).trans (by omega)

end Cslib.Crypto.GGM
