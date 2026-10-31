/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Turing
public import Complexity.Computability.WordRAM.OfTuring

/-!
# Polynomial time on the word RAM and on multi-tape Turing machines

A function with binary output is computable in polynomial time by a multi-tape Turing machine
(`Turing.MultiTapeTM.ComputableInPolyTime`) exactly when one fixed word-RAM program computes it
on the bits of its input within polynomially many instructions, at every word size above a
polynomial threshold. The two directions are the simulation of Turing machines by the word RAM
(`Cslib.WordRAM.OfTuring`) and the simulation of the word RAM by Turing machines
(`Cslib.WordRAM.Program.ComputesInTime.turingComputableInPolyTime_of_width`) [Cook and
Reckhow][CookReckhow1973].

## Conventions

* **Input.** The instance `a` is given to the program as its bits, the word list
  `(encIn a).map Bool.toNat`, placed as in `State.init`.
* **Output.** The program returns `f a` as one word; the machine writes it in binary (`encNat`).
* **Word size.** Since one word holds the output, whose bit length is bounded only by the running
  time, the threshold `W |encIn a|` is polynomial rather than logarithmic. For decision problems a
  logarithmic threshold suffices: see `Cslib.WordRAM.mem_P_iff_uniformPolynomialTime`.
* **Basis.** Any basis containing `Basis.additive` whose checked operations are polynomial-time,
  such as `Basis.additive`, `Basis.arithmetic` and `Basis.standard`.

## Main results

* `Cslib.WordRAM.computableInPolyTime_map_toNat`: the bits of an instance, as words, are
  computable in polynomial time.
* `Cslib.WordRAM.turingComputableInPolyTime_iff_exists_computesInTime`: Turing-machine polynomial
  time is uniform polynomial word-RAM time at polynomial word sizes.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM

variable {B : Basis} {α : Type} {encIn : α ↪ List Bool}

/-- The bits of an instance, as words framed as a list of binary naturals, are computable in
polynomial time from the instance. -/
theorem computableInPolyTime_map_toNat (encIn : α ↪ List Bool) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun a => (encIn a).map Bool.toNat) encIn
      (encList encNat) :=
  (Turing.MultiTapeTM.ComputableInPolyTime.map
    (Turing.MultiTapeTM.ComputableInPolyTime.of_finite Bool.toNat)).comp
    ((bits_encList_polyTime encBool).1.comp
      (Turing.MultiTapeTM.ComputableInPolyTime.of_eq fun _ => rfl))

/-- **Turing-machine polynomial time is word-RAM polynomial time.** Over any basis `B` containing
`Basis.additive` whose checked operations are polynomial-time, a function `f` with binary output is
computable in polynomial time by a multi-tape Turing machine exactly when one fixed word-RAM program
over `B` computes it on the bits `(encIn a).map Bool.toNat` of its input, within `T |encIn a|`
instructions at every word size of at least `W |encIn a|`, for polynomially bounded `T` and `W`. -/
theorem turingComputableInPolyTime_iff_exists_computesInTime (φ : Basis.additive.Hom B)
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat)) {f : α → ℕ} :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encNat ↔
      ∃ (r : ℕ) (p : Program B r) (T W : ℕ → ℕ), PolynomiallyBounded T ∧
        PolynomiallyBounded W ∧ p.ComputesInTime (fun _ a => (encIn a).map Bool.toNat)
          (fun a _ => T (encIn a).length) (fun a w => W (encIn a).length ≤ w) f := by
  constructor
  · intro h
    obtain ⟨r, p, T, W, hT, hW, hp⟩ := h.exists_wordRAM_nat
    exact ⟨r, p.mapOp φ, T, W, hT, hW, hp.mapOp φ⟩
  · rintro ⟨r, p, T, W, hT, hW, hp⟩
    -- Simulate at a computable width above `W |encIn a|` and the input length.
    obtain ⟨width, hwidth, hge⟩ := exists_unary_majorant (encIn := encIn)
      (u := fun a => W (encIn a).length + (encIn a).length + 1)
      (((PolyBounded.of_polynomiallyBounded _ hW).add PolyBounded.self).add (.const 1))
    refine hp.turingComputableInPolyTime_of_width hop hwidth
      (fun a => by have := hge a; omega) (fun a => ⟨?_, fun v hv => ?_⟩)
      (computableInPolyTime_map_toNat encIn)
      ((PolyBounded.of_polynomiallyBounded _ hT).comp PolyBounded.self)
    · have := hge a
      rw [List.length_map]
      exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hv
      have := hge a
      exact (Bool.toNat_le b).trans_lt
        (Nat.one_lt_two_pow_iff.2 (by omega))

end Cslib.WordRAM
