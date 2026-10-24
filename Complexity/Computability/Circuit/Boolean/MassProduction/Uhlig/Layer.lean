/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Uhlig
public import Complexity.Computability.Circuit.Boolean.Synthesis
public import Complexity.Computability.Circuit.Replication
public import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# One layer of Uhlig's construction

Split the input of `f` into a prefix of `p` bits and a suffix of `w` bits. For each of the
`2 ^ p` prefixes, the restriction of `f` is a function of the suffix. Uhlig's code of these
restrictions gives `2 ^ p + 1` resource functions on `w` bits (`resource`). Group `2 t` copies
into `t` pairs. In each pair, every resource reads the suffix of the copy that uses it
(`BitString.Uhlig.first`, `BitString.Uhlig.second`); each copy then sums its resources. Hence
`t` copies of every resource yield `2 t` copies of `f`, at an overhead linear in `t`.

The routing and decoding gates are disjunctive normal forms of the two prefixes in a pair, so
their number is polynomial in `2 ^ p` and `w`. This is far from optimal, but it is negligible in
the recursion of `Uhlig`, where `2 ^ p` is polynomial in the input length.

Sizes count all gates, including constants and negations. The theorem bounds circuit size; it
does not certify the running time of any circuit constructor.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Uhlig.restriction`: the restrictions of `f` to
  prefixes, numbered by `BitString.equivFin`.
* `Cslib.Circuits.Boolean.MassProduction.Uhlig.resource`: Uhlig's resource functions.
* `Cslib.Circuits.Boolean.MassProduction.Uhlig.rank`,
  `Cslib.Circuits.Boolean.MassProduction.Uhlig.pairCopy`,
  `Cslib.Circuits.Boolean.MassProduction.Uhlig.pairWires`,
  `Cslib.Circuits.Boolean.MassProduction.Uhlig.pairSelect`,
  `Cslib.Circuits.Boolean.MassProduction.Uhlig.routedBit`,
  `Cslib.Circuits.Boolean.MassProduction.Uhlig.decoded`: prefix ranking, pair wiring, suffix
  routing, and resource decoding.
* `Cslib.Circuits.Boolean.MassProduction.Uhlig.selectorCost`,
  `Cslib.Circuits.Boolean.MassProduction.Uhlig.layerOverhead`: the DNF selector cost and per-pair
  gate budget.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.Uhlig.complexity_directProduct_two_mul_le`: if every
  function on `w` inputs has `t` copies of size at most `B`, every function on `p + w` inputs
  has `2 t` copies of size at most `(2 ^ p + 1) * B + t * layerOverhead p w`.

## References

* [D. Uhlig, *Networks computing Boolean functions for multiple input values*][Uhlig1992].
* [I. Wegener, *The Complexity of Boolean Functions*][Wegener1987], proof of Theorem 10.2.3.
* Simplifies MassProduction/UhligRoutingCircuit.lean, MassProduction/UhligDecoder.lean and
  MassProduction/UhligLayer.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Uhlig

open Finset BitString.Uhlig

variable {p w t : ℕ}

/-- The restriction of `f` to prefix number `a`, as a function of the suffix `z`. It is false
when `a` numbers no prefix. -/
def restriction (f : BooleanFunction (p + w)) (z : BitString w) (a : ℕ) : Bool :=
  if h : a < 2 ^ p then f (Fin.append ((BitString.equivFin p).symm ⟨a, h⟩) z) else false

/-- Resource `j` of Uhlig's construction: position `j` of the code of the restrictions. -/
def resource (f : BooleanFunction (p + w)) (j : ℕ) : BooleanFunction w :=
  fun z => code (restriction f z) j

/-- At index `2 ^ p`, out of range of `p`-bit prefixes, `restriction f z (2 ^ p)` is `false`. -/
@[simp] theorem restriction_two_pow (f : BooleanFunction (p + w)) (z : BitString w) :
    restriction f z (2 ^ p) = false := by
  simp [restriction]

/-- Restricting to the number of the actual prefix evaluates `f`. -/
theorem restriction_equivFin (f : BooleanFunction (p + w)) (x : BitString (p + w)) :
    restriction f (x ∘ Fin.natAdd p) (BitString.equivFin p (x ∘ Fin.castAdd w)) = f x := by
  simp only [restriction, Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  exact congrArg f Fin.append_castAdd_natAdd

/-- The number of the prefix of copy `c`. -/
def rank {k : ℕ} (x : BitString (k * (p + w))) (c : Fin k) : ℕ :=
  BitString.equivFin p (directProductInput x c ∘ Fin.castAdd w)

/-- Copy `s` of pair `i`: pair `i` consists of copies `i` and `t + i`. -/
abbrev pairCopy (s : Fin 2) (i : Fin t) : Fin (2 * t) :=
  finProdFinEquiv (s, i)

/-- The prefix wires of both copies of pair `i`. -/
def pairWires (i : Fin t) : Fin (p + p) → Fin (2 * t * (p + w)) :=
  Fin.append (fun a => finProdFinEquiv (pairCopy 0 i, Fin.castAdd w a))
    (fun a => finProdFinEquiv (pairCopy 1 i, Fin.castAdd w a))

/-- Whether copy `s` of a pair uses code position `j`, read from the pair's two prefixes. -/
def pairSelect (s : Fin 2) (j : ℕ) (q : BitString (p + p)) : Bool :=
  ![first, second] s (BitString.equivFin p (q ∘ Fin.castAdd p))
    (BitString.equivFin p (q ∘ Fin.natAdd p)) j

/-- Composing `pairSelect` with `pairWires i` selects code positions from the prefix ranks of the
two copies in pair `i`. -/
theorem pairSelect_comp_pairWires (s : Fin 2) (j : ℕ) (i : Fin t)
    (x : BitString (2 * t * (p + w))) :
    pairSelect s j (x ∘ pairWires i) =
      ![first, second] s (rank x (pairCopy 0 i)) (rank x (pairCopy 1 i)) j := by
  have h0 : (x ∘ pairWires i) ∘ Fin.castAdd p =
      directProductInput x (pairCopy 0 i) ∘ Fin.castAdd w := by
    funext a
    simp only [pairWires, directProductInput, Function.comp_apply, Fin.append_left]
  have h1 : (x ∘ pairWires i) ∘ Fin.natAdd p =
      directProductInput x (pairCopy 1 i) ∘ Fin.castAdd w := by
    funext a
    simp only [pairWires, directProductInput, Function.comp_apply, Fin.append_right]
  simp only [pairSelect, rank, h0, h1]

/-- The suffix bit `k` routed to resource `j` from pair `i`. -/
def routedBit (j : ℕ) (i : Fin t) (k : Fin w) (x : BitString (2 * t * (p + w))) : Bool :=
  if first (rank x (pairCopy 0 i)) (rank x (pairCopy 1 i)) j then
    x (finProdFinEquiv (pairCopy 0 i, Fin.natAdd p k))
  else x (finProdFinEquiv (pairCopy 1 i, Fin.natAdd p k))

/-- The gate budget of one disjunctive normal form over the two prefixes of a pair. -/
abbrev selectorCost (p : ℕ) : ℕ :=
  2 ^ (p + p) * (2 * (p + p) + 2) + 1

/-- The gates spent on each pair, besides the resource circuits. -/
def layerOverhead (p w : ℕ) : ℕ :=
  (2 ^ p + 1) * (w * (2 * selectorCost p + 4) + 2 * (selectorCost p + 5)) + 2

private theorem synthesis_routedBit (j : ℕ) (i : Fin t) (k : Fin w) :
    Synthesis interpretation (inputs (2 * t * (p + w))) {routedBit j i k}
      (2 * selectorCost p + 4) := by
  have hφ := Synthesis.selected (pairWires (p := p) (w := w) i) (pairSelect 0 j)
  have hy (s : Fin 2) : Synthesis interpretation (inputs (2 * t * (p + w)))
      {fun x => x (finProdFinEquiv (pairCopy s i, Fin.natAdd p k))} 0 :=
    Synthesis.of_mem ⟨_, rfl⟩
  refine ((hφ.and (hy 0)).or (hφ.not.and (hy 1))).congr_iff (fun x => ?_) |>.mono
    Set.Subset.rfl Set.Subset.rfl (by unfold selectorCost; omega)
  simp only [routedBit, pairSelect_comp_pairWires, Matrix.cons_val_zero]
  by_cases h : first (rank x (pairCopy 0 i)) (rank x (pairCopy 1 i)) j = true <;> simp [h]

/-- The decoded output of copy `s` of pair `i`, reading the bank outputs after the inputs. -/
def decoded (s : Fin 2) (i : Fin t) (y : BitString (2 * t * (p + w) + (2 ^ p + 1) * t)) :
    Bool :=
  ∑ j : Fin (2 ^ p + 1), (pairSelect s j (y ∘ Fin.castAdd _ ∘ pairWires i) &&
    y (Fin.natAdd _ (finProdFinEquiv (j, i))))

private theorem synthesis_decoded (s : Fin 2) (i : Fin t) :
    Synthesis interpretation (inputs (2 * t * (p + w) + (2 ^ p + 1) * t)) {decoded s i}
      ((2 ^ p + 1) * (selectorCost p + 5) + 1) := by
  have h := Synthesis.sum (s := inputs (2 * t * (p + w) + (2 ^ p + 1) * t)) univ
    (fun (j : Fin (2 ^ p + 1)) y => pairSelect s j (y ∘ Fin.castAdd _ ∘ pairWires i) &&
      y (Fin.natAdd _ (finProdFinEquiv (j, i))))
    (fun _ => selectorCost p + 1)
    fun j _ => (Synthesis.selected _ _).and (Synthesis.of_mem ⟨_, rfl⟩)
  refine h.mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- If the decoder reads the inputs and, for every resource, its value on the routed
suffixes of pair `i`, then copy `s` of pair `i` decodes to `f` on that copy's input. -/
theorem decoded_eq (f : BooleanFunction (p + w)) (s : Fin 2) (i : Fin t)
    (x : BitString (2 * t * (p + w))) (y : BitString (2 * t * (p + w) + (2 ^ p + 1) * t))
    (hx : y ∘ Fin.castAdd _ = x)
    (hy : ∀ j : Fin (2 ^ p + 1), y (Fin.natAdd _ (finProdFinEquiv (j, i))) =
      resource f j (if first (rank x (pairCopy 0 i)) (rank x (pairCopy 1 i)) j then
        directProductInput x (pairCopy 0 i) ∘ Fin.natAdd p
      else directProductInput x (pairCopy 1 i) ∘ Fin.natAdd p)) :
    decoded s i y = f (directProductInput x (pairCopy s i)) := by
  have hrank (c : Fin (2 * t)) : rank x c < 2 ^ p := Fin.is_lt _
  simp only [decoded] at hy ⊢
  rw [← Function.comp_assoc, hx]
  simp only [pairSelect_comp_pairWires, hy, resource]
  rw [Fin.sum_univ_eq_sum_range (fun j => ![first, second] s (rank x (pairCopy 0 i))
    (rank x (pairCopy 1 i)) j && code (restriction f (if first (rank x (pairCopy 0 i))
      (rank x (pairCopy 1 i)) j then directProductInput x (pairCopy 0 i) ∘ Fin.natAdd p
    else directProductInput x (pairCopy 1 i) ∘ Fin.natAdd p)) j)]
  match s with
  | 0 =>
    rw [Matrix.cons_val_zero, sum_first_code_route (restriction_two_pow f) (hrank _)]
    exact restriction_equivFin f _
  | 1 =>
    change ∑ j ∈ range _, (second _ _ j && _) = _
    rw [sum_second_code_route (restriction_two_pow f) (hrank _)]
    exact restriction_equivFin f _

/-- **One layer of Uhlig's construction.** If every function on `w` inputs has `t`
independent copies of size at most `B`, then every function on `p + w` inputs has `2 t`
independent copies of size at most `(2 ^ p + 1) * B + t * layerOverhead p w`. -/
theorem complexity_directProduct_two_mul_le {B : ℕ}
    (hB : ∀ g : BooleanFunction w, complexity interpretation (directProduct g t) ≤ B)
    (f : BooleanFunction (p + w)) :
    complexity interpretation (directProduct f (2 * t)) ≤
      (2 ^ p + 1) * B + t * layerOverhead p w := by
  -- The front passes the inputs through and routes suffixes to the resource bank.
  let front : Fin (2 * t * (p + w) + (2 ^ p + 1) * (t * w)) →
      BooleanFunction (2 * t * (p + w)) :=
    Fin.append (fun l x => x l) fun q x =>
      routedBit (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm (finProdFinEquiv.symm q).2).1
        (finProdFinEquiv.symm (finProdFinEquiv.symm q).2).2 x
  obtain ⟨cFront, hcFront, hsFront⟩ := Synthesis.exists_circuit_outputs
    (Synthesis.family front (Fin.append (fun _ => 0) fun _ => 2 * selectorCost p + 4)
      (Fin.addCases (fun l => by
          simpa [front] using Synthesis.of_mem (I := interpretation)
            (s := inputs (2 * t * (p + w))) (f := fun x => x l) ⟨l, rfl⟩)
        fun q => by simpa [front] using synthesis_routedBit _ _ _))
  -- The bank evaluates `t` copies of every resource.
  choose bank hbank hsBank using fun j : Fin (2 ^ p + 1) =>
    complexity_le_iff.mp (hB (resource f j))
  -- The decoder sums each copy's resources.
  obtain ⟨cDec, hcDec, hsDec⟩ := Synthesis.exists_circuit_outputs
    (Synthesis.family (fun c => decoded (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2)
      (fun _ => (2 ^ p + 1) * (selectorCost p + 5) + 1) fun c => synthesis_decoded _ _)
  let layer := cDec.comp
    (((Circuit.id signature _).parallel (Circuit.parallelFamily bank)).comp cFront)
  refine complexity_le_iff.mpr ⟨layer, fun x => ?_, ?_⟩
  · have hfront : cFront.eval interpretation x = Fin.append x fun q =>
        routedBit (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm (finProdFinEquiv.symm q).2).1
          (finProdFinEquiv.symm (finProdFinEquiv.symm q).2).2 x := by
      rw [hcFront x]
      funext l
      refine Fin.addCases (fun l => ?_) (fun q => ?_) l <;> simp [front]
    funext c
    obtain ⟨⟨s, i⟩, rfl⟩ := finProdFinEquiv.surjective c
    simp only [layer, Circuit.eval_comp, hcDec _, hfront, Circuit.eval_parallel,
      Fin.append_comp_castAdd, Fin.append_comp_natAdd, Circuit.eval_wiring, Function.comp_id,
      Equiv.symm_apply_apply]
    refine decoded_eq f s i x _ (by simp) fun j => ?_
    rw [Fin.append_right, Circuit.eval_parallelFamily_apply, hbank j]
    simp only [directProduct, resource]
    congr 2
    funext k
    simp only [directProductInput, Equiv.symm_apply_apply, routedBit]
    split <;> rfl
  · have hbankSize : ∑ j, (bank j).size ≤ (2 ^ p + 1) * B := by
      simpa using Finset.sum_le_sum fun j (_ : j ∈ univ) => hsBank j
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul, mul_zero, zero_add] at hsFront hsDec
    simp only [layer, Circuit.size_comp, Circuit.size_parallel, Circuit.size_parallelFamily,
      Circuit.size_wiring, zero_add]
    refine (Nat.add_le_add (Nat.add_le_add hsFront hbankSize) hsDec).trans (le_of_eq ?_)
    unfold layerOverhead
    ring

end Cslib.Circuits.Boolean.MassProduction.Uhlig
