/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BoundedSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Exponential
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Bounded existential quantification in exponential time

A test `f` that is computable in polynomial time can be tried on every word of length `ℓ x`,
for `ℓ` computable in polynomial time, within time `2 ^ O(|x| + ℓ x)`
(`Cslib.Complexity.exists_computableInO_any_enumList`). The candidates are streamed in place by
`Turing.MultiTapeTM.ComputableInO.exists_bits`, with independent time and space bounds.
Every polynomial in the cost is absorbed by the exponential, so the exponent is linear in
`|x| + ℓ x`, with a constant
that depends on the test.

The shared search gives the closure of `PSPACE` under bounded existential quantification
(`Cslib.Complexity.setOf_exists_mem_PSPACE`), where the point is the space of the run. Here the
time is the point: this brute force is the last step of lazy diagonalization for
nondeterministic time, which must decide deterministically whether some certificate is
accepted.

## Main definitions

* `Cslib.Complexity.boundedExistsEdge`: the edges of the two-step reachability problem.

## Main results

* `Cslib.Complexity.savitch_boundedExistsEdge`: Savitch's algorithm at depth `1` on these edges
  decides the bounded existential.
* `Cslib.Complexity.exists_computableInO_any_enumList`: the bounded existential within time and
  space `2 ^ O(|x| + ℓ x)`.
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- The edges of the graph on words of width `n + 1` whose reachability within two steps from the
all-zero word to the all-one word is a bounded existential over `f`: an edge from the all-zero word
to `true :: w` when `f (x, w)`, and from every word starting with `true` to the all-one word. -/
@[expose] def boundedExistsEdge {β : Type} (f : β × List Bool → Bool) (x : β) (u v : List Bool) :
    Bool :=
  if !(u.any fun b => b) && v.headD false then f (x, v.tail)
  else u.headD false && !(v.any fun b => !b)

/-- Savitch's algorithm at depth `1` on the edges of `Cslib.Complexity.boundedExistsEdge` decides
the bounded existential. -/
theorem savitch_boundedExistsEdge {β : Type} (f : β × List Bool → Bool) (x : β) (n : ℕ) :
    Cslib.Reachability.savitch (boundedExistsEdge f x) (n + 1) 1 (List.replicate (n + 1) false)
      (List.replicate (n + 1) true) = true ↔ ∃ w : List Bool, w.length = n ∧ f (x, w) = true := by
  rw [Cslib.Reachability.savitch_eq]
  simp only [Cslib.Reachability.reach, List.any_eq_true, Cslib.BitString.mem_enumList,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨m, hm, h₁ | h₁, h₂ | h₂⟩
    · subst h₁
      exact absurd h₂ (by simp [List.replicate_succ])
    · subst h₁
      refine ⟨List.replicate n true, List.length_replicate .., ?_⟩
      simpa [boundedExistsEdge, List.replicate_succ] using h₂
    · subst h₂
      refine ⟨List.replicate n true, List.length_replicate .., ?_⟩
      simpa [boundedExistsEdge, List.replicate_succ] using h₁
    · obtain ⟨b, w, rfl⟩ := List.exists_cons_of_length_eq_add_one hm
      refine ⟨w, by simpa using hm, ?_⟩
      cases b <;> simp_all [boundedExistsEdge, List.replicate_succ]
  · rintro ⟨w, hw, hf⟩
    refine ⟨true :: w, by simp [hw], Or.inr ?_, Or.inr ?_⟩
    · simp [boundedExistsEdge, List.replicate_succ, hf]
    · simp [boundedExistsEdge, List.replicate_succ]

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd'
    ComputableInPolyTime.bool_and' in
/-- **Bounded existential quantification in exponential time.** If a test `f` is computable within
time and space polynomial in its encoded input, and `ℓ` is computable in unary in polynomial time,
then whether some word of length `ℓ x` passes `f` with `x` is computable within time and space
`2 ^ (K * ((encB x).length + ℓ x))` for a constant `K`. The native bounded search reuses workspace
and visits every candidate once. -/
theorem exists_computableInO_any_enumList {β : Type} {encB : β ↪ List Bool}
    {f : β × List Bool → Bool} {Tf Sf : β × List Bool → ℕ}
    (hf : ComputableInO f (encPair encB encBits) encBool Tf Sf)
    (hTf : PolyBounded (fun q => (encPair encB encBits q).length) Tf)
    (hSf : PolyBounded (fun q => (encPair encB encBits q).length) Sf)
    {ℓ : β → ℕ} (hℓ : ComputableInPolyTime ℓ encB encUnary) :
    ∃ K, ComputableInO (fun x => (Cslib.BitString.enumList (ℓ x)).any fun w => f (x, w)) encB
      encBool (fun x => 2 ^ (K * ((encB x).length + ℓ x)))
      (fun x => 2 ^ (K * ((encB x).length + ℓ x))) := by
  let size := fun p : β × ℕ => (encPair encB encUnary p).length
  obtain ⟨a, b, ht⟩ := hTf.exists_le
  obtain ⟨c, d, hs⟩ := hSf.exists_le
  let T := fun p : β × ℕ => a * (size p + 1) ^ b
  let S := fun p : β × ℕ => c * (size p + 1) ^ d
  have hT : PolyBounded size T := PolyBounded.of_forall_le a b fun _ => le_rfl
  have hS : PolyBounded size S := PolyBounded.of_forall_le c d fun _ => le_rfl
  obtain ⟨overhead, ho, h⟩ := hf.exists_bits (T := T) (S := S)
    (fun p w hw => by
      apply (ht (p.1, w)).trans_eq
      simp only [T, size, length_encPair, encBits_apply, encUnary_apply,
        List.length_replicate, hw])
    (fun p w hw => by
      apply (hs (p.1, w)).trans_eq
      simp only [S, size, length_encPair, encBits_apply, encUnary_apply,
        List.length_replicate, hw])
  obtain ⟨C, hC⟩ := PolyBounded.exists_le_mul_two_pow ((ho.add hT).add hS)
  have hin : ComputableInPolyTime (fun x => (x, ℓ x)) encB (encPair encB encUnary) :=
    ComputableInPolyTime.id'.prod hℓ
  obtain ⟨Ti, Si, hTi, hSi, hi⟩ := hin.exists_computableInO
  obtain ⟨CI, hCI⟩ := PolyBounded.exists_le_mul_two_pow hTi
  obtain ⟨CJ, hCJ⟩ := PolyBounded.exists_le_mul_two_pow hSi
  refine ⟨3, (h.comp hi).mono (8 * (CI + CJ + C + 1)) (fun x => ?_) (fun x => ?_)⟩
  all_goals
    set n := (encB x).length
    set L := ℓ x
    have hcost := hC (x, L)
    simp only [length_encPair, encUnary_apply, List.length_replicate] at hcost
    change overhead (x, L) + T (x, L) + S (x, L) ≤ C * 2 ^ (2 * n + 1 + L) at hcost
    have hI : 2 ^ n ≤ 2 ^ (3 * (n + L)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hprod : 2 ^ L * 2 ^ (2 * n + 1 + L) ≤ 2 * 2 ^ (3 * (n + L)) := by
      calc
        _ = 2 ^ (2 * (n + L) + 1) := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 ^ (3 * (n + L) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = _ := by rw [pow_succ, Nat.mul_comm]
    have hcount : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have hsingle : 2 ^ (2 * n + 1 + L) ≤ 2 * 2 ^ (3 * (n + L)) := by
      have := Nat.mul_le_mul_right (2 ^ (2 * n + 1 + L)) hcount
      nlinarith
    have hdouble : (2 ^ L + 1) * 2 ^ (2 * n + 1 + L) ≤
        4 * 2 ^ (3 * (n + L)) := by nlinarith
    have hnonzero : 1 ≤ 2 ^ (3 * (n + L)) := Nat.one_le_two_pow
  · change Ti x + (2 ^ L + 1) * (overhead (x, L) + T (x, L)) ≤
      8 * (CI + CJ + C + 1) * (2 ^ (3 * (n + L)) + 1)
    have hiT := hCI x
    change Ti x ≤ CI * 2 ^ n at hiT
    have htest : overhead (x, L) + T (x, L) ≤ C * 2 ^ (2 * n + 1 + L) := by omega
    have hscaled := Nat.mul_le_mul_left (2 ^ L + 1) htest
    have hexp := Nat.mul_le_mul_left C hdouble
    have hi' := Nat.mul_le_mul_left CI hI
    nlinarith
  · change Si x + (overhead (x, L) + S (x, L)) ≤
      8 * (CI + CJ + C + 1) * (2 ^ (3 * (n + L)) + 1)
    have hiS := hCJ x
    change Si x ≤ CJ * 2 ^ n at hiS
    have htest : overhead (x, L) + S (x, L) ≤ C * 2 ^ (2 * n + 1 + L) := by omega
    have hexp := Nat.mul_le_mul_left C hsingle
    have hi' := Nat.mul_le_mul_left CJ hI
    nlinarith

end Cslib.Complexity
