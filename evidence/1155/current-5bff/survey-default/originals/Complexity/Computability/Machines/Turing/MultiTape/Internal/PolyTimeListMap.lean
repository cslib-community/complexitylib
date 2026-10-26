/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup

/-! # Direct mapping with the complete original input

The existing captured fold retains the original input while appending each callback result.
Its prefix bound follows from the list's encoded length and the callback machine's own clock.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime
open Cslib

/-- Map with the complete original input captured uniformly by one joint callback machine.
The list certificate fixes its element encoding before the callback is checked. -/
@[fun_prop]
theorem mapWithInput {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {f : γ → α → β} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hf : ComputableInPolyTime (fun p : γ × α => f p.1 p.2) (encPair encIn encA) encB) :
    ComputableInPolyTime (fun x => (list x).map (f x)) encIn (encList encB) := by
  obtain ⟨c, d, hsize⟩ := hf.polyBounded_length.exists_le
  obtain ⟨cl, dl, hlistSize⟩ := hlist.polyBounded_length.exists_le
  let L := fun n : ℕ => n + cl * (n + 1) ^ dl
  let bound := fun n : ℕ => L n * (2 * (c * (3 * L n + 3) ^ d) + 1)
  have hb : PolynomiallyBounded bound := by dsimp [bound, L]; fun_prop
  have houter := fst (encPair encIn (encList encB)) encA
  have hvalue := snd (encPair encIn (encList encB)) encA
  have hstep : ComputableInPolyTime
      (fun q : (γ × List β) × α => q.1.2 ++ [f q.1.1 q.2])
      (encPair (encPair encIn (encList encB)) encA) (encList encB) :=
    (snoc encB).comp (houter.snd'.prod (hf.comp (houter.fst'.prod hvalue)))
  have hfold := foldlWith (encA := encA) (encL := encList encA) (encP := encIn)
    (encB := encList encB) (par := id) (list := list) (init := fun _ => [])
    (step := fun x mapped value => mapped ++ [f x value]) id' hlist (const []) hstep
    (PolyBounded.of_polynomiallyBounded (fun x => (encIn x).length) hb) (by
      intro x i _
      simp only [foldlMap, List.nil_append, id_eq]
      have hlistBound : (encList encA (list x)).length ≤ L (encIn x).length :=
        (hlistSize x).trans (by dsimp [L]; omega)
      have heach : ∀ b ∈ ((list x).take i).map (f x),
          (encB b).length ≤ c * (3 * L (encIn x).length + 3) ^ d := by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        have hain := (List.take_sublist i (list x)).subset ha
        have haBound := (SizedListEncoding.length_elem_le
          (encA := encA) (encL := encList encA) (list x) a hain).trans hlistBound
        apply (hsize (x, a)).trans
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        simp only [length_encPair]
        have hx : (encIn x).length ≤ L (encIn x).length := by dsimp [L]; omega
        omega
      apply (length_encList_le encB _ heach).trans
      dsimp [bound]
      apply Nat.mul_le_mul_right
      simp only [List.length_map, List.length_take]
      exact (Nat.min_le_right i (list x).length).trans
        ((SizedListEncoding.length_le (encA := encA) (encL := encList encA) (list x)).trans
          hlistBound))
  simpa only [foldlMap, List.nil_append, id_eq] using hfold

end Turing.MultiTapeTM.ComputableInPolyTime
