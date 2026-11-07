/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.ModEq

/-!
# `SYM ∘ AND` circuits

A depth-two `SYM ∘ AND` circuit on inputs `ι` (`Circuits.Boolean.SymAnd`) is a finite multiset of
AND gates, each given by the finite set of input positions it reads, below one symmetric gate
`out : ℕ → Bool` applied to the number of satisfied AND gates, counted with multiplicity. This is
the target model of the Yao and Beigel–Tarui simulation of ACC⁰ [BeigelTarui1994, Theorem 1.1]
(their `SYM⁺` circuits) and the representation consumed by Williams's ACC satisfiability
algorithm [Williams2014]. The AND gates read positive literals only; negations are absorbed by the
polynomial constructions that produce such circuits.

The size of a circuit is the number of AND gates (`SymAnd.size`) and its fan-in is the largest
AND fan-in (`SymAnd.fanIn`). Read in a commutative ring, the number of satisfied AND gates is a sum
of monomials (`SymAnd.natCast_count_eq_sum`). Conversely, an integer-valued function of degree at
most `D` on the cube agrees modulo any positive `M` with the number of satisfied AND gates in a
multiset of at most `M * (n + 1) ^ D` gates of fan-in at most `D`
(`SymAnd.exists_countP_modEq_of_mem_lowDegree`): each integer coefficient is replaced by its
least nonnegative residue modulo `M`.

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd`: depth-two `SYM ∘ AND` circuits.
* `Cslib.Circuits.Boolean.SymAnd.count`, `SymAnd.eval`, `SymAnd.size`, `SymAnd.fanIn`.
* `Cslib.Circuits.Boolean.SymAnd.slot`: the circuit reading a single input.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.natCast_count_eq_sum`: the count as a sum of monomials.
* `Cslib.Circuits.Boolean.SymAnd.exists_countP_modEq_of_mem_lowDegree`: low-degree integer
  functions are AND counts modulo `M`.

## References

* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean

open Finset BitString

/-- A depth-two `SYM ∘ AND` circuit on inputs `ι`: a multiset of AND gates, each reading the
positive literals of a finite set of positions, below a symmetric output gate `out`, which sees
only the number of satisfied AND gates. -/
structure SymAnd (ι : Type*) where
  /-- The AND gates, as the sets of positions they read, with multiplicity. -/
  gates : Multiset (Finset ι)
  /-- The symmetric output gate, applied to the number of satisfied AND gates. -/
  out : ℕ → Bool

namespace SymAnd

variable {ι : Type*}

/-- The number of AND gates of `C` satisfied by `x`, counted with multiplicity. -/
@[expose] def count (C : SymAnd ι) (x : ι → Bool) : ℕ :=
  C.gates.countP fun S => ∀ i ∈ S, x i = true

/-- The output of `C` on `x`: the symmetric gate applied to the number of satisfied AND gates. -/
@[expose] def eval (C : SymAnd ι) (x : ι → Bool) : Bool :=
  C.out (C.count x)

/-- The size of `C`: its number of AND gates, counted with multiplicity. -/
@[expose] def size (C : SymAnd ι) : ℕ :=
  Multiset.card C.gates

/-- The fan-in of `C`: the largest fan-in of its AND gates (`0` without gates). -/
@[expose] def fanIn (C : SymAnd ι) : ℕ :=
  (C.gates.map Finset.card).sup

/-- The fan-in is at most `f` exactly when every AND gate reads at most `f` positions. -/
theorem fanIn_le_iff {C : SymAnd ι} {f : ℕ} : C.fanIn ≤ f ↔ ∀ S ∈ C.gates, #S ≤ f := by
  simp only [fanIn, Multiset.sup_le, Multiset.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-- Every AND gate reads at most `C.fanIn` positions. -/
theorem card_le_fanIn {C : SymAnd ι} {S : Finset ι} (hS : S ∈ C.gates) : #S ≤ C.fanIn :=
  fanIn_le_iff.1 le_rfl S hS

/-- At most all the AND gates are satisfied. -/
theorem count_le_size (C : SymAnd ι) (x : ι → Bool) : C.count x ≤ C.size :=
  Multiset.countP_le_card _ _

/-- Read in a commutative ring, the number of sets in `G` all of whose positions are true at `x`
is the sum of their monomials at `x`. -/
theorem natCast_countP_eq_sum {R : Type*} [CommRing R] (G : Multiset (Finset ι))
    (x : ι → Bool) :
    ((G.countP fun S => ∀ i ∈ S, x i = true : ℕ) : R) = (G.map fun S => monomial R S x).sum := by
  induction G using Multiset.induction_on with
  | empty => simp
  | cons S G ih =>
    rw [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, ih,
      monomial_apply]
    split_ifs <;> simp [add_comm]

/-- Read in a commutative ring, the number of satisfied AND gates is the sum of the monomials of
the gates. -/
theorem natCast_count_eq_sum {R : Type*} [CommRing R] (C : SymAnd ι) (x : ι → Bool) :
    (C.count x : R) = (C.gates.map fun S => monomial R S x).sum :=
  natCast_countP_eq_sum C.gates x

/-- **Low-degree integer functions are AND counts modulo `M`.** For `c` of degree at most `D` on
the cube and `M > 0`, some multiset of at most `M * (n + 1) ^ D` sets of at most `D` positions
has, at every point, a number of satisfied sets congruent to `c` modulo `M`: take each monomial of
`c` with multiplicity its coefficient's least nonnegative residue modulo `M`. -/
theorem exists_countP_modEq_of_mem_lowDegree [Fintype ι] {D : ℕ} {c : (ι → Bool) → ℤ}
    (hc : c ∈ lowDegree ℤ ι D) {M : ℕ} (hM : 0 < M) :
    ∃ G : Multiset (Finset ι), (∀ S ∈ G, #S ≤ D) ∧
      Multiset.card G ≤ M * (Fintype.card ι + 1) ^ D ∧
      ∀ x, ((G.countP fun S => ∀ i ∈ S, x i = true : ℕ) : ℤ) ≡ c x [ZMOD M] := by
  classical
  have hspan : monomial ℤ '' {S : Finset ι | #S ≤ D} =
      Set.range fun S : {S : Finset ι // #S ≤ D} => monomial ℤ (S : Finset ι) := by
    ext f
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Subtype.exists, exists_prop]
  rw [lowDegree, hspan, Submodule.mem_span_range_iff_exists_fun] at hc
  obtain ⟨a, ha⟩ := hc
  refine ⟨(Finset.univ : Finset {S : Finset ι // #S ≤ D}).val.bind fun S =>
      Multiset.replicate (a S % M).toNat (S : Finset ι), ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨T, -, hT⟩ := Multiset.mem_bind.1 hS
    rw [Multiset.eq_of_mem_replicate hT]
    exact T.2
  · rw [Multiset.card_bind]
    change ∑ S, Multiset.card (Multiset.replicate (a S % M).toNat (S : Finset ι)) ≤ _
    simp only [Multiset.card_replicate]
    calc ∑ S, (a S % M).toNat ≤ ∑ _S : {S : Finset ι // #S ≤ D}, M :=
          Finset.sum_le_sum fun S _ => by
            rw [Int.toNat_le]
            exact (Int.emod_lt_of_pos _ (by exact_mod_cast hM)).le
      _ = M * Fintype.card {S : Finset ι // #S ≤ D} := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ M * (Fintype.card ι + 1) ^ D := by
          refine Nat.mul_le_mul_left M ?_
          rw [Fintype.card_subtype]
          exact card_filter_card_le_le_pow D
  · intro x
    rw [natCast_countP_eq_sum, Multiset.map_bind, Multiset.sum_bind, ← ha]
    simp only [Multiset.map_replicate, Multiset.sum_replicate, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, nsmul_eq_mul]
    change ∑ S, _ ≡ _ [ZMOD M]
    refine Int.ModEq.sum fun S _ => Int.ModEq.mul_right _ ?_
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hM.ne'))]
    exact Int.mod_modEq _ _

/-- The `SYM ∘ AND` circuit reading the single input `t`: one AND gate `{t}` and the output
"at least one satisfied gate". -/
def slot (t : ι) : SymAnd ι :=
  ⟨{{t}}, fun z => decide (z ≠ 0)⟩

/-- The circuit `slot t` outputs the input bit at `t`. -/
@[simp] theorem eval_slot (t : ι) (x : ι → Bool) : (slot t).eval x = x t := by
  rw [eval, count, slot, show ({{t}} : Multiset (Finset ι)) = {t} ::ₘ 0 from rfl,
    Multiset.countP_cons, Multiset.countP_zero]
  cases h : x t <;> simp [h]

/-- The circuit `slot t` has one AND gate. -/
@[simp] theorem size_slot (t : ι) : (slot t).size = 1 := by
  simp only [size, slot, Multiset.card_singleton]

/-- The circuit `slot t` has fan-in one. -/
@[simp] theorem fanIn_slot (t : ι) : (slot t).fanIn = 1 := by
  simp [slot, fanIn]

end SymAnd

end Cslib.Circuits.Boolean
