/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Yates
public import CslibFrontier.Computability.Circuit.Boolean.SymAnd

/-!
# Evaluating a `SYM ∘ AND` circuit on all inputs

Williams's **Evaluation Lemma** ([Williams2014], Lemma 4.2, numbered as in the author's full
version of 31 July 2012): a `SYM ∘ AND` circuit with `s` AND gates on `n` inputs can be evaluated on
all `2 ^ n` inputs in `(2 ^ n + poly(s)) · poly(n)` time, given a `poly(s)`-time evaluator for its
symmetric gate. This file formalizes the source's first proof (dynamic programming, after
Björklund) in the unit-cost time monad `Cslib.Algorithms.Lean.TimeM`.

Let `f S` be the number of AND gates reading exactly the positions `S` (`gateMultiplicity`). The
number of AND gates satisfied by the input with true positions `T` is
`g T = ∑_{S ⊆ T} f S`, the zeta transform of `f` (`count_eq_subsetZeta`). The algorithm
`truthTableM` builds the table of `f` (`multiplicityM`), computes `g` by Yates's algorithm
(`Cslib.Algorithms.Lean.Yates.zetaM`), tabulates the symmetric gate on `0, …, s` with the supplied
costed evaluator `outM`, and reads off the output for every input.

## Source-to-Lean mapping

* The source's `SYM⁺` circuit `C''` with `s''` AND gates `G_j ⊆ [n]` is a
  `C : Circuits.Boolean.SymAnd (Fin n)` with `C.size = s`, presented to the algorithm as a list
  `gates` of the gate sets with `(gates : Multiset _) = C.gates`. Such a list always exists
  (`C.gates.toList`), but `Multiset.toList` is noncomputable, so concrete runs supply the list
  explicitly.
* The table `f` is `(multiplicityM gates).ret`, and `g` is `(zetaM (multiplicityM gates).ret).ret`.
* The `i`-th variable assignment is the bit string `(BitString.equivFin n).symm k` of cell `k`,
  with coordinate `0` the least significant bit; `V[k] = 1` iff the circuit outputs `1` there is
  `getElem_ret_truthTableM`.
* The symmetric function "evaluated in `poly(s)` time" is a costed evaluator
  `outM : ℕ → TimeM ℕ Bool` agreeing with `C.out` on `0, …, s` and costing at most `T` ticks there.
  As everywhere in `TimeM`, these ticks are `outM`'s own (trusted) annotation of its cost.
* The running time `(2 ^ n + poly(s)) · poly(n)` is the exact bound
  `(n + 2) * (2 ^ n + (s + 1) * (T + 1))` of `truthTableM_spec`, which is
  `(2 ^ n + poly(s)) · poly(n)` when `T = poly(s)`. The source's hypothesis `s ≤ 2^{0.1 n}` is not
  assumed: in Proof 1 it only absorbs the `s · poly(n)` cost of building the table into `O(2 ^ n)`,
  and the bound here keeps that term explicit. (The source's Proof 2, by rectangular matrix
  multiplication, does use it; that proof is not formalized.)

## Cost model

* **Charged:** initializing the multiplicity table (`2 ^ n` ticks); locating and incrementing the
  cell of one AND gate from its position set (`n + 1` ticks per gate); one tick per cell per pass of
  Yates's algorithm (`n * 2 ^ n` ticks, see `CslibFrontier.Algorithms.Lean.Yates`); one tick per
  symmetric-gate value tabulated plus the cost of `outM` itself (`s + 1` values); one tick per
  output cell (`2 ^ n` ticks), covering the table lookup.
* **Uncharged:** loop control and vector allocation.

This is a unit-cost model with words of `O(n + log s)` bits (indices of cells and AND counts at
most `s`). It is not Turing-machine time, and the evaluator is not constructed from a circuit
encoding here; a Turing-machine or word-RAM realization is not formalized.

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.gateMultiplicity`: the number of AND gates reading exactly `S`.
* `Cslib.Circuits.Boolean.SymAnd.multiplicityM`: the table of multiplicities, in `TimeM`.
* `Cslib.Circuits.Boolean.SymAnd.truthTableM`: the truth table of the circuit, in `TimeM`.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.count_eq_subsetZeta`: the AND count is a zeta transform.
* `Cslib.Circuits.Boolean.SymAnd.getElem_ret_truthTableM`, `ret_truthTableM`: correctness.
* `Cslib.Circuits.Boolean.SymAnd.time_truthTableM`, `time_truthTableM_le`: the exact cost and its
  bound.
* `Cslib.Circuits.Boolean.SymAnd.truthTableM_spec`: the Evaluation Lemma, correctness together
  with the bound `(n + 2) * (2 ^ n + (s + 1) * (T + 1))`.

## References

* [A. Björklund, T. Husfeldt, M. Koivisto, *Set Partitioning via
  Inclusion–Exclusion*][BjorklundHusfeldtKoivisto2009]
* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
-/

public section

namespace Cslib.Circuits.Boolean.SymAnd

open Finset Cslib.BitString Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TimeM
  Cslib.Algorithms.Lean.Yates

section Count

variable {ι : Type*} [DecidableEq ι]

/-- The number of AND gates of `C` reading exactly the positions `S`. -/
@[expose] def gateMultiplicity (C : SymAnd ι) (S : Finset ι) : ℕ :=
  C.gates.count S

/-- **The AND count is a zeta transform**: the number of AND gates satisfied by the input with
true positions `T` is `∑_{S ⊆ T} gateMultiplicity C S`. -/
theorem count_eq_subsetZeta (C : SymAnd ι) (T : Finset ι) :
    C.count (fun i => decide (i ∈ T)) = subsetZeta C.gateMultiplicity T := by
  obtain ⟨gates, out⟩ := C
  simp only [count, subsetZeta, gateMultiplicity]
  induction gates using Multiset.induction_on with
  | empty => simp
  | cons G gs ih =>
    rw [Multiset.countP_cons, ih]
    simp only [Multiset.count_cons, sum_add_distrib, sum_ite_eq', mem_powerset]
    congr 1
    by_cases h : G ⊆ T
    · rw [ite_eq_left h, ite_eq_left fun i hi => decide_eq_true (h hi)]
    · rw [ite_eq_right h, ite_eq_right fun hG => h fun i hi => of_decide_eq_true (hG i hi)]

/-- The AND count at an arbitrary input, over finitely many positions, as a zeta transform. -/
theorem count_eq_subsetZeta_filter [Fintype ι] (C : SymAnd ι) (x : ι → Bool) :
    C.count x = subsetZeta C.gateMultiplicity (univ.filter fun i => x i = true) := by
  rw [← count_eq_subsetZeta]
  congr 1 with i : 1
  cases h : x i <;> simp [h]

end Count

variable {n : ℕ}

/-- The table of multiplicities: start from `2 ^ n` zeros, then for each AND gate increment the
cell of its position set. -/
@[expose] def multiplicityM (gates : List (Finset (Fin n))) : TimeM ℕ (Vector ℕ (2 ^ n)) := do
  ✓[2 ^ n] gates.foldlM (fun t G => do
    ✓[n + 1] pure (t.set (maskIndex G : ℕ) (t[(maskIndex G : ℕ)] + 1) (maskIndex G).isLt))
    (Vector.replicate (2 ^ n) 0)

private theorem getElem_foldl_multiplicity (gates : List (Finset (Fin n)))
    (t : Vector ℕ (2 ^ n)) (k : ℕ) (hk : k < 2 ^ n) :
    (gates.foldl (fun t G =>
      (t.set (maskIndex G : ℕ) (t[(maskIndex G : ℕ)] + 1) (maskIndex G).isLt)) t)[k] =
      t[k] + gates.count (maskSet n k) := by
  induction gates generalizing t with
  | nil => simp
  | cons G gs ih =>
    rw [List.foldl_cons, ih, List.count_cons, Vector.getElem_set]
    by_cases h : (maskIndex G : ℕ) = k
    · have hG : G = maskSet n k := by rw [← h, maskSet_maskIndex]
      rw [ite_eq_left h, ite_eq_left (beq_iff_eq.mpr hG)]
      subst h
      omega
    · have hG : G ≠ maskSet n k := by
        rintro rfl
        exact h (congrArg Fin.val (maskIndex_maskSet ⟨k, hk⟩))
      rw [ite_eq_right h, ite_eq_right fun h' => hG (beq_iff_eq.mp h'), add_zero]

/-- The cell of `S` in the table of multiplicities holds the number of gates reading `S`. -/
theorem getElem_ret_multiplicityM (gates : List (Finset (Fin n))) (k : ℕ) (hk : k < 2 ^ n) :
    (multiplicityM gates).ret[k] = gates.count (maskSet n k) := by
  simp only [multiplicityM, ret_bind, ret_foldlM, ret_pure]
  rw [getElem_foldl_multiplicity, Vector.getElem_replicate, zero_add]

/-- Building the table of multiplicities takes `2 ^ n + s * (n + 1)` ticks. -/
@[simp] theorem time_multiplicityM (gates : List (Finset (Fin n))) :
    (multiplicityM gates).time = 2 ^ n + gates.length * (n + 1) := by
  simp only [multiplicityM, time_bind, time_tick]
  rw [time_foldlM_of_time_eq _ _ _ (c := n + 1)]
  intro acc a
  simp only [time_bind, time_tick, time_pure, add_zero]

/-- **Williams's evaluation algorithm**: the table of multiplicities, its zeta transform by Yates's
algorithm, the symmetric gate tabulated on `0, …, s` by `outM`, and one lookup per input. -/
@[expose] def truthTableM (gates : List (Finset (Fin n))) (outM : ℕ → TimeM ℕ Bool) :
    TimeM ℕ (Vector Bool (2 ^ n)) := do
  let m ← multiplicityM gates
  let g ← zetaM m
  let table ← Vector.ofFnM fun j : Fin (gates.length + 1) => do ✓ outM j
  Vector.ofFnM fun k : Fin (2 ^ n) => do
    ✓ pure (if h : g[(k : ℕ)] < gates.length + 1 then table[g[(k : ℕ)]] else false)

/-- **Correctness of the evaluation algorithm**: cell `k` of the output is the value of the
circuit at the bit string of `k`. -/
theorem getElem_ret_truthTableM (C : SymAnd (Fin n)) (gates : List (Finset (Fin n)))
    (hgates : (gates : Multiset (Finset (Fin n))) = C.gates) (outM : ℕ → TimeM ℕ Bool)
    (hout : ∀ j ≤ C.size, (outM j).ret = C.out j) (k : Fin (2 ^ n)) :
    (truthTableM gates outM).ret[(k : ℕ)] = C.eval ((BitString.equivFin n).symm k) := by
  have hsize : C.size = gates.length := by rw [size, ← hgates, Multiset.coe_card]
  have hm : ∀ (j : ℕ) (hj : j < 2 ^ n),
      (multiplicityM gates).ret[j] = C.gateMultiplicity (maskSet n j) := by
    intro j hj
    rw [getElem_ret_multiplicityM, gateMultiplicity, ← hgates, Multiset.coe_count]
  have hg : (zetaM (multiplicityM gates).ret).ret[(k : ℕ)] =
      C.count ((BitString.equivFin n).symm k) := by
    rw [getElem_ret_zetaM _ _ hm _ k.isLt, equivFin_symm_eq_decide_mem_maskSet,
      count_eq_subsetZeta]
  have hle : C.count ((BitString.equivFin n).symm k) < gates.length + 1 := by
    have := C.count_le_size ((BitString.equivFin n).symm k)
    omega
  simp only [truthTableM, ret_bind, ret_vectorOfFnM, Vector.getElem_ofFn, ret_pure]
  simp only [hg, dite_eq_left hle]
  rw [hout _ (by omega)]
  rfl

/-- **Correctness of the evaluation algorithm**, as a vector: the output is the truth table of
the circuit, listed in the order of `BitString.equivFin`. -/
theorem ret_truthTableM (C : SymAnd (Fin n)) (gates : List (Finset (Fin n)))
    (hgates : (gates : Multiset (Finset (Fin n))) = C.gates) (outM : ℕ → TimeM ℕ Bool)
    (hout : ∀ j ≤ C.size, (outM j).ret = C.out j) :
    (truthTableM gates outM).ret = Vector.ofFn fun k => C.eval ((BitString.equivFin n).symm k) := by
  ext k hk
  rw [Vector.getElem_ofFn]
  exact getElem_ret_truthTableM C gates hgates outM hout ⟨k, hk⟩

/-- The exact cost of the evaluation algorithm. -/
theorem time_truthTableM (gates : List (Finset (Fin n))) (outM : ℕ → TimeM ℕ Bool) :
    (truthTableM gates outM).time = (n + 2) * 2 ^ n + (n + 2) * gates.length + 1 +
      ∑ j ∈ range (gates.length + 1), (outM j).time := by
  simp only [truthTableM, time_bind, time_multiplicityM, time_zetaM, time_vectorOfFnM,
    time_tick, time_pure, add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun j => 1 + (outM j).time), sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_range, smul_eq_mul,
    mul_one]
  ring

/-- **The cost bound**: if the symmetric gate costs at most `T` on `0, …, s`, the evaluation
algorithm takes at most `(n + 2) * 2 ^ n + (s + 1) * (n + 2 + T)` ticks. -/
theorem time_truthTableM_le (gates : List (Finset (Fin n))) (outM : ℕ → TimeM ℕ Bool) {T : ℕ}
    (htime : ∀ j ≤ gates.length, (outM j).time ≤ T) :
    (truthTableM gates outM).time ≤ (n + 2) * 2 ^ n + (gates.length + 1) * (n + 2 + T) := by
  rw [time_truthTableM]
  have hsum : ∑ j ∈ range (gates.length + 1), (outM j).time ≤ (gates.length + 1) * T := by
    calc ∑ j ∈ range (gates.length + 1), (outM j).time
        ≤ ∑ _j ∈ range (gates.length + 1), T :=
          sum_le_sum fun j hj => htime j (Nat.lt_succ_iff.mp (mem_range.mp hj))
      _ = (gates.length + 1) * T := by rw [sum_const, card_range, smul_eq_mul]
  nlinarith

/-- **Williams's Evaluation Lemma** ([Williams2014], Lemma 4.2, Proof 1). Let `C` be a
`SYM ∘ AND` circuit with `s = C.size` AND gates on `n` inputs, given as a list `gates` of its gate
sets, and let `outM` evaluate the symmetric gate correctly on `0, …, s` in at most `T` ticks. Then
`truthTableM gates outM` returns the truth table of `C` in at most
`(n + 2) * (2 ^ n + (s + 1) * (T + 1))` ticks, which is `(2 ^ n + poly(s)) · poly(n)` for
`T = poly(s)`. -/
theorem truthTableM_spec (C : SymAnd (Fin n)) (gates : List (Finset (Fin n)))
    (hgates : (gates : Multiset (Finset (Fin n))) = C.gates) (outM : ℕ → TimeM ℕ Bool) {T : ℕ}
    (hout : ∀ j ≤ C.size, (outM j).ret = C.out j) (htime : ∀ j ≤ C.size, (outM j).time ≤ T) :
    (truthTableM gates outM).ret = Vector.ofFn (fun k => C.eval ((BitString.equivFin n).symm k)) ∧
      (truthTableM gates outM).time ≤ (n + 2) * (2 ^ n + (C.size + 1) * (T + 1)) := by
  have hsize : C.size = gates.length := by rw [size, ← hgates, Multiset.coe_card]
  refine ⟨ret_truthTableM C gates hgates outM hout, ?_⟩
  rw [hsize] at htime ⊢
  have hT : n + 2 + T ≤ (n + 2) * (T + 1) := by nlinarith
  calc (truthTableM gates outM).time
      ≤ (n + 2) * 2 ^ n + (gates.length + 1) * (n + 2 + T) := time_truthTableM_le gates outM htime
    _ ≤ (n + 2) * 2 ^ n + (gates.length + 1) * ((n + 2) * (T + 1)) := by gcongr
    _ = (n + 2) * (2 ^ n + (gates.length + 1) * (T + 1)) := by ring

end Cslib.Circuits.Boolean.SymAnd
