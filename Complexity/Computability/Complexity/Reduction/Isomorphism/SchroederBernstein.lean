/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Reduction.Isomorphism
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time Cantor–Schröder–Bernstein

Berman and Hartmanis proved a polynomial-time analogue of the Cantor–Schröder–Bernstein theorem
[Berman and Hartmanis][BermanHartmanis1977]: if `A ≤ B` and `B ≤ A` via one-one,
length-increasing reductions with polynomial-time left inverses, then `A` and `B` are
polynomial-time isomorphic.

## Construction

Let `f : α → β` and `g : β → α` be the two reductions, with polynomial-time left inverses
`f' : β → α` and `g' : α → β`. Starting from `a : α`, walk backwards through the alternating chain
of preimages `a ← g' a ← f' (g' a) ← ⋯`, at each step checking whether the current element lies
in the range of `g` (resp. `f`) by testing `g (g' x) = x` (resp. `f (f' y) = y`). Because both
reductions strictly increase encoded length, each double step strictly decreases `(encA x).length`,
so the walk stops after at most `(encA a).length` double steps. If it stops on the `α` side, map `a`
to `f a`, otherwise to `g' a`. The walk runs in polynomial time via the library's iteration
combinator, and the resulting map is a bijection whose inverse is the same construction with the
roles of the two sides exchanged.

Compared with the source, which works over strings, the statement here holds for arbitrary
types `α`, `β` with injective encodings into `List Bool`. Only left inverses are assumed: the
injectivity of `f` and `g` follows from them.

## Main results

* `Cslib.Complexity.polyTime_schroeder_bernstein`: polynomial-time computable, length-increasing
  maps with polynomial-time left inverses in both directions yield an equivalence `e : α ≃ β` with
  `e` and `e.symm` polynomial-time computable and `e a = f a ∨ g (e a) = a` for every `a`.
* `Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeIsomorphic`:
  mutual `≤₁,ᵢₗ` reducibility implies `≅ᵖ`.

## References

* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace PolyTimeSchroederBernstein

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

/-- Fuelled ancestor walk: `chain f f' g g' n a` is `true` when the backward chain from `a` stops on
the `α` side (or the fuel runs out), and `false` when it stops on the `β` side. -/
private def chain [DecidableEq α] [DecidableEq β] (f : α → β) (f' : β → α) (g : β → α)
    (g' : α → β) : ℕ → α → Bool
  | 0, _ => true
  | n + 1, a =>
    if g (g' a) = a then
      if f (f' (g' a)) = g' a then chain f f' g g' n (f' (g' a)) else false
    else true

variable [DecidableEq α] [DecidableEq β]

private theorem chain_zero (f : α → β) (f' : β → α) (g : β → α) (g' : α → β) (a : α) :
    chain f f' g g' 0 a = true := rfl

private theorem chain_succ (f : α → β) (f' : β → α) (g : β → α) (g' : α → β) (n : ℕ) (a : α) :
    chain f f' g g' (n + 1) a =
      if g (g' a) = a then
        if f (f' (g' a)) = g' a then chain f f' g g' n (f' (g' a)) else false
      else true := rfl

section
variable {f : α → β} {f' : β → α} {g : β → α} {g' : α → β}
  (hf : ∀ a, (encA a).length < (encB (f a)).length)
  (hg : ∀ b, (encB b).length < (encA (g b)).length)

include hf hg in
/-- Fuel beyond the encoded length does not change the outcome of the walk. -/
private theorem chain_eq_of_le : ∀ (n m : ℕ) (a : α), (encA a).length ≤ n → (encA a).length ≤ m →
    chain f f' g g' n a = chain f f' g g' m a := by
  intro n
  induction n with
  | zero =>
    intro m a hn hm
    cases m with
    | zero => rfl
    | succ m =>
      have ha : g (g' a) ≠ a := by
        intro h
        have := hg (g' a)
        rw [h] at this
        omega
      simp only [chain_zero, chain_succ, ha, ↓reduceIte]
  | succ n ih =>
    intro m a hn hm
    cases m with
    | zero =>
      have ha : g (g' a) ≠ a := by
        intro h
        have := hg (g' a)
        rw [h] at this
        omega
      simp only [chain_zero, chain_succ, ha, ↓reduceIte]
    | succ m =>
      simp only [chain_succ]
      by_cases ha : g (g' a) = a
      · by_cases hb : f (f' (g' a)) = g' a
        · simp only [ha, hb, ↓reduceIte]
          have h1 := hg (g' a)
          have h2 := hf (f' (g' a))
          rw [ha] at h1
          rw [hb] at h2
          exact ih m _ (by omega) (by omega)
        · simp only [ha, hb, ↓reduceIte]
      · simp only [ha, ↓reduceIte]

end

/-- The backward chain from `a` stops on the `α` side. -/
private def stop (encA : α ↪ List Bool) (f : α → β) (f' : β → α) (g : β → α) (g' : α → β)
    (a : α) : Bool :=
  chain f f' g g' (encA a).length a

section
variable {f : α → β} {f' : β → α} {g : β → α} {g' : α → β}
  (hf : ∀ a, (encA a).length < (encB (f a)).length)
  (hg : ∀ b, (encB b).length < (encA (g b)).length)

include hf hg in
/-- Unfolding equation for `stop`. -/
private theorem stop_eq (a : α) : stop encA f f' g g' a =
    if g (g' a) = a then
      if f (f' (g' a)) = g' a then stop encA f f' g g' (f' (g' a)) else false
    else true := by
  unfold stop
  by_cases ha : g (g' a) = a
  · by_cases hb : f (f' (g' a)) = g' a
    · have h1 := hg (g' a)
      have h2 := hf (f' (g' a))
      rw [ha] at h1
      rw [hb] at h2
      obtain ⟨n, hn⟩ : ∃ n, (encA a).length = n + 1 := ⟨(encA a).length - 1, by omega⟩
      rw [hn, chain_succ, ite_eq_left ha, ite_eq_left hb, ite_eq_left ha, ite_eq_left hb]
      exact chain_eq_of_le hf hg _ _ _ (by omega) le_rfl
    · cases h : (encA a).length with
      | zero =>
        exfalso
        have := hg (g' a)
        rw [ha] at this
        omega
      | succ n => simp only [chain_succ, ha, hb, ↓reduceIte]
  · cases h : (encA a).length with
    | zero => simp only [chain_zero, ha, ↓reduceIte]
    | succ n => simp only [chain_succ, ha, ↓reduceIte]

include hf hg in
/-- Swapping the roles of the two sides negates the side on which a chain stops. -/
private theorem stop_swap : ∀ (n : ℕ) (b : β), (encB b).length ≤ n → f (f' b) = b →
    stop encB g g' f f' b = !stop encA f f' g g' (f' b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hn hb
    rw [stop_eq hg hf b, stop_eq hf hg (f' b)]
    simp only [ite_eq_left hb]
    by_cases hc : g (g' (f' b)) = f' b
    · simp only [ite_eq_left hc]
      by_cases hd : f (f' (g' (f' b))) = g' (f' b)
      · simp only [ite_eq_left hd]
        have h1 := hg (g' (f' b))
        have h2 := hf (f' b)
        rw [hc] at h1
        rw [hb] at h2
        exact ih _ (by omega) _ le_rfl hd
      · simp only [ite_eq_right hd]
        rw [stop_eq hg hf _, ite_eq_right hd]
        rfl
    · simp only [ite_eq_right hc]
      rfl

end

section Bijection
variable {f : α → β} {f' : β → α} {g : β → α} {g' : α → β}
  (hf : ∀ a, (encA a).length < (encB (f a)).length)
  (hg : ∀ b, (encB b).length < (encA (g b)).length)
  (hff : Function.LeftInverse f' f) (hgg : Function.LeftInverse g' g)

/-- The forward map: `f` on chains stopping on the `α` side, `g⁻¹` otherwise. -/
private def fwd (encA : α ↪ List Bool) (f : α → β) (f' : β → α) (g : β → α) (g' : α → β)
    (a : α) : β :=
  if stop encA f f' g g' a then f a else g' a

include hf hg hff in
private theorem stop_f (a : α) : stop encB g g' f f' (f a) = !stop encA f f' g g' a := by
  have h := stop_swap (f' := f') (g' := g') hf hg _ (f a) le_rfl (by rw [hff a])
  rwa [hff a] at h

include hf hg hgg in
private theorem stop_g (b : β) : stop encA f f' g g' (g b) = !stop encB g g' f f' b := by
  have h := stop_swap (f' := g') (g' := f') hg hf _ (g b) le_rfl (by rw [hgg b])
  rwa [hgg b] at h

include hf hg in
/-- A chain that does not stop on the `α` side starts with a `g`-parent. -/
private theorem g_g'_of_stop_eq_false {a : α} (h : stop encA f f' g g' a = false) :
    g (g' a) = a := by
  by_contra hc
  rw [stop_eq hf hg, ite_eq_right hc] at h
  exact Bool.noConfusion h

include hf hg hff hgg in
private theorem fwd_bwd_left (a : α) : fwd encB g g' f f' (fwd encA f f' g g' a) = a := by
  unfold fwd
  cases h : stop encA f f' g g' a
  · have hga := g_g'_of_stop_eq_false (f' := f') hf hg h
    have hs : stop encB g g' f f' (g' a) = true := by
      have := stop_g (f' := f') hf hg hgg (g' a)
      rw [hga, h] at this
      revert this
      cases stop encB g g' f f' (g' a) <;> decide
    simp only [Bool.false_eq_true, ↓reduceIte, hs, hga]
  · simp only [↓reduceIte, stop_f (g' := g') hf hg hff a, h, Bool.not_true, Bool.false_eq_true,
      hff a]

end Bijection

/-! ### The walk as a polynomial-time loop -/

/-- One step of the ancestor walk on states `(current element, stopped, side)`. -/
private def step (f : α → β) (f' : β → α) (g : β → α) (g' : α → β) (s : α × Bool × Bool) :
    α × Bool × Bool :=
  if s.2.1 then s else
    if g (g' s.1) = s.1 then
      if f (f' (g' s.1)) = g' s.1 then (f' (g' s.1), false, true) else (s.1, true, false)
    else (s.1, true, true)

private theorem step_iterate_done (f : α → β) (f' : β → α) (g : β → α) (g' : α → β)
    (x : α) (r : Bool) (n : ℕ) : (step f f' g g')^[n] (x, true, r) = (x, true, r) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

private theorem step_iterate (f : α → β) (f' : β → α) (g : β → α) (g' : α → β) (n : ℕ) (a : α) :
    ((step f f' g g')^[n] (a, false, true)).2.2 = chain f f' g g' n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, chain_succ]
    by_cases ha : g (g' a) = a
    · by_cases hb : f (f' (g' a)) = g' a
      · simp only [step, ha, hb, ↓reduceIte, Bool.false_eq_true]
        exact ih _
      · simp only [step, ha, hb, ↓reduceIte, Bool.false_eq_true, step_iterate_done]
    · simp only [step, ha, ↓reduceIte, Bool.false_eq_true, step_iterate_done]

section Loop
variable {f : α → β} {f' : β → α} {g : β → α} {g' : α → β}
  (hf : ∀ a, (encA a).length < (encB (f a)).length)
  (hg : ∀ b, (encB b).length < (encA (g b)).length)

include hf hg in
private theorem length_step_le (s : α × Bool × Bool) :
    (encA (step f f' g g' s).1).length ≤ (encA s.1).length := by
  unfold step
  split_ifs with h1 h2 h3
  · exact le_rfl
  · have := hg (g' s.1)
    have := hf (f' (g' s.1))
    rw [h2] at *
    rw [h3] at *
    simp only
    omega
  · exact le_rfl
  · exact le_rfl

include hf hg in
private theorem length_step_iterate_le (n : ℕ) (s : α × Bool × Bool) :
    (encA ((step f f' g g')^[n] s).1).length ≤ (encA s.1).length := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (length_step_le hf hg s)

end Loop

section PolyTime
variable {f : α → β} {f' : β → α} {g : β → α} {g' : α → β}
  (hf : ∀ a, (encA a).length < (encB (f a)).length)
  (hg : ∀ b, (encB b).length < (encA (g b)).length)
  (pf : ComputableInPolyTime f encA encB) (pf' : ComputableInPolyTime f' encB encA)
  (pg : ComputableInPolyTime g encB encA) (pg' : ComputableInPolyTime g' encA encB)

include pf pf' pg pg' in
private theorem computableInPolyTime_step :
    ComputableInPolyTime (step f f' g g') (encPair encA (encPair encBool encBool))
      (encPair encA (encPair encBool encBool)) := by
  unfold step
  fun_prop

include hf hg pf pf' pg pg' in
private theorem computableInPolyTime_stop :
    ComputableInPolyTime (stop encA f f' g g') encA encBool := by
  have hloop : ComputableInPolyTime
      (fun a => (step f f' g g')^[(encA a).length] (a, false, true)) encA
      (encPair encA (encPair encBool encBool)) := by
    refine ComputableInPolyTime.iterate (bound := fun a => 2 * (encA a).length + 5)
      (ComputableInPolyTime.encoding_length encA) (by fun_prop)
      (computableInPolyTime_step pf pf' pg pg')
      (PolyBounded.of_forall_le 5 1 fun a => by nlinarith) fun a i _ => ?_
    have := length_step_iterate_le (f' := f') (g' := g') hf hg i (a, false, true)
    simp only [length_encPair, encBool_apply, List.length_singleton] at this ⊢
    omega
  have h := ComputableInPolyTime.snd' (ComputableInPolyTime.snd' hloop)
  refine h.of_enc_eq fun a => ?_
  rw [stop, ← step_iterate]

include hf hg pf pf' pg pg' in
private theorem computableInPolyTime_fwd :
    ComputableInPolyTime (fwd encA f f' g g') encA encB := by
  have := computableInPolyTime_stop hf hg pf pf' pg pg'
  unfold fwd
  fun_prop

end PolyTime

end PolyTimeSchroederBernstein

open PolyTimeSchroederBernstein in
/-- **Polynomial-time Cantor–Schröder–Bernstein** [Berman and Hartmanis][BermanHartmanis1977].

If `f : α → β` and `g : β → α` are polynomial-time computable, strictly increase encoded length,
and have polynomial-time left inverses `f'` and `g'`, then there is an equivalence `e : α ≃ β`
such that `e` and `e.symm` are polynomial-time computable and every `e a` is either `f a` or a
`g`-preimage of `a`. The bijection is decided by walking the alternating chain of preimages
backwards; length-increase bounds the walk by the input length. -/
theorem polyTime_schroeder_bernstein {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → β} {f' : β → α} {g : β → α} {g' : α → β}
    (pf : ComputableInPolyTime f encA encB) (pf' : ComputableInPolyTime f' encB encA)
    (pg : ComputableInPolyTime g encB encA) (pg' : ComputableInPolyTime g' encA encB)
    (hff : Function.LeftInverse f' f) (hgg : Function.LeftInverse g' g)
    (hf : ∀ a, (encA a).length < (encB (f a)).length)
    (hg : ∀ b, (encB b).length < (encA (g b)).length) :
    ∃ e : α ≃ β, (ComputableInPolyTime e encA encB ∧ ComputableInPolyTime e.symm encB encA) ∧
      ∀ a, e a = f a ∨ g (e a) = a := by
  classical
  refine ⟨⟨fwd encA f f' g g', fwd encB g g' f f', fwd_bwd_left hf hg hff hgg,
    fwd_bwd_left hg hf hgg hff⟩,
    ⟨computableInPolyTime_fwd hf hg pf pf' pg pg', computableInPolyTime_fwd hg hf pg pg' pf pf'⟩,
    fun a => ?_⟩
  change fwd encA f f' g g' a = f a ∨ g (fwd encA f f' g g' a) = a
  unfold fwd
  cases h : stop encA f f' g g' a
  · exact Or.inr (by simpa only [Bool.false_eq_true, ↓reduceIte] using
      g_g'_of_stop_eq_false (f' := f') hf hg h)
  · exact Or.inl (by simp only [↓reduceIte])

/-- **Berman–Hartmanis isomorphism theorem** [Berman and Hartmanis][BermanHartmanis1977]: if
`A ≤₁,ᵢₗ B` and `B ≤₁,ᵢₗ A`, that is, each reduces to the other by a length-increasing one-one
reduction with a polynomial-time left inverse, then `A ≅ᵖ B`. -/
theorem PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeIsomorphic
    {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
    (hAB : PolyTimeInvertibleLengthIncreasingOneOneReducible encA encB A B)
    (hBA : PolyTimeInvertibleLengthIncreasingOneOneReducible encB encA B A) :
    PolyTimeIsomorphic encA encB A B := by
  obtain ⟨f, ⟨f', pf, pf', hff, hf⟩, hfAB⟩ := hAB
  obtain ⟨g, ⟨g', pg, pg', hgg, hg⟩, hgBA⟩ := hBA
  obtain ⟨e, he, hmem⟩ := polyTime_schroeder_bernstein pf pf' pg pg' hff hgg hf hg
  refine ⟨e, he, fun a => ?_⟩
  rcases hmem a with h | h
  · rw [h, hfAB]
  · conv_lhs => rw [← h]
    exact (hgBA (e a)).symm

end Cslib.Complexity
