/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Foundations.Data.BitString.List

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Combinatorics.Lautemann
import Complexity.Foundations.Combinatorics.MajorityVote
import Complexity.Foundations.Data.List.OfFn

/-!
# The Sipser–Lautemann theorem

Every problem in `BPP` lies in the second level `Σ₂ ∩ Π₂` of the polynomial hierarchy, and hence
in `PH`. This is the Sipser–Gács–Lautemann theorem: [Sipser][Sipser1983] placed `BPP` in `PH`,
Gács improved the placement to `Σ₂ ∩ Π₂`, and [Lautemann][Lautemann1983] gave the proof
formalised here; see also [Arora and Barak, Theorem 7.15][AroraBarak09].

Given a `BPP` verifier `V` using random strings of length `m = p (enc a).length`, repeating the
test `2 R` times (with `R = 6 m + 48`) and taking a strict majority (`> R` accepting runs) reduces
the error fraction to at most `(8 / 9) ^ R` (`Cslib.card_filter_card_filter_le_le`). The amplified
seeds `Seed m = (Fin (2 R) → BitString m)` form an additive group under bitwise xor, to which
Lautemann's covering lemma applies:

* **Completeness** (`a ∈ A`): since `2 ^ (2 R m) * (8 ^ R) ^ (2 R) < (9 ^ R) ^ (2 R)`, the covering
  lemma (`Cslib.exists_forall_exists_add_mem_of_card_mul_card_compl_pow_lt`) yields `T = 2 R`
  shift vectors covering the entire space of amplified seeds.
* **Soundness** (`a ∉ A`): for any `T = 2 R` shift vectors, each shifted accepting set has size at
  most `(8 / 9) ^ R` of the seed space, and `T * 8 ^ R < 9 ^ R`, so their union cannot cover all
  amplified seeds (`Cslib.exists_forall_add_notMem_of_mul_card_lt`).

The resulting `Σ₂` verifier `SipserLautemann.verifier` reads a concatenated certificate `w = u ++ r`
with existential block length `T * (2 R m)` and universal block length `2 R m`, reconstructs each
shifted trial seed as the bitwise xor of two fixed-width rows of `w` (`Cslib.BitString.listRow`),
and checks whether some shift yields more than `R` accepting trials. Seeds and shift tables are
read from bit strings through the block views `Cslib.BitString.ofList` and
`Cslib.BitString.block`. Closure of `BPP` under complement (`Cslib.Complexity.compl_mem_BPP`) and
quantifier duality (`Cslib.Complexity.compl_mem_PiP_of_mem_SigmaP`) then give
`BPP enc ⊆ PiP 2 enc` without repeating the construction.

## Main definitions

* `Cslib.Complexity.SipserLautemann.Seed`,
  `Cslib.Complexity.SipserLautemann.majorityAccepts`: amplified seeds and strict majority
  acceptance. Seeds are shifted by pointwise bit-string addition (`+`).
* `Cslib.Complexity.SipserLautemann.verifier`: the `Σ₂` matrix verifier for a `BPP` problem.
* `Cslib.Complexity.SipserLautemann.witnessPoly`, `Cslib.Complexity.SipserLautemann.seedPoly`:
  the polynomial block lengths of the existential shift table and universal seed.

## Main results

* `Cslib.Complexity.SipserLautemann.exists_shifts_majorityAccepts`,
  `Cslib.Complexity.SipserLautemann.exists_seed_not_majorityAccepts`: combinatorial completeness and
  soundness of shifted majority votes.
* `Cslib.Complexity.SipserLautemann.verifier_polyTime`: the matrix verifier is computable in
  polynomial time.
* `Cslib.Complexity.SipserLautemann.isAlternatingVerifier_verifier`: the matrix verifier is a valid
  `Σ₂` alternating verifier for any `BPP` problem.
* `Cslib.Complexity.BPP_subset_SigmaP_two`: `BPP enc ⊆ SigmaP 2 enc`.
* `Cslib.Complexity.BPP_subset_PiP_two`: `BPP enc ⊆ PiP 2 enc`.
* `Cslib.Complexity.BPP_subset_SigmaP_two_inter_PiP_two`: `BPP enc ⊆ SigmaP 2 enc ∩ PiP 2 enc`.
* `Cslib.Complexity.BPP_subset_PH`: `BPP enc ⊆ PH enc`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 7.15][AroraBarak09]
* [M. Sipser, *A complexity theoretic approach to randomness*][Sipser1983]
* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

namespace SipserLautemann

/-! ### Amplification and shift parameters -/

/-- Half the number of majority-amplification trials for a single-trial seed of length `m`:
`6 * m + 48 = 6 * (m + 7) + 6`. -/
def halfRuns (m : ℕ) : ℕ := 6 * m + 48

/-- Number of independent repetitions in majority amplification: `2 * halfRuns m = 12 * m + 96`.
A run accepts when strictly more than `halfRuns m` of the `runs m` trials accept. -/
def runs (m : ℕ) : ℕ := 2 * halfRuns m

/-- Number of shift vectors in the Lautemann cover: `shifts m = runs m = 12 * m + 96`. -/
def shifts (m : ℕ) : ℕ := runs m

/-- Length of an amplified universal seed: `runs m * m` bits. -/
def seedLen (m : ℕ) : ℕ := runs m * m

/-- Length of the existential witness concatenating `shifts m` shift vectors:
`shifts m * seedLen m` bits. -/
def witnessLen (m : ℕ) : ℕ := shifts m * seedLen m

/-- Polynomial giving `runs (p.eval n)` at input length `n`. -/
noncomputable def runsPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2 * (Polynomial.C 6 * p + Polynomial.C 48)

/-- Polynomial giving `seedLen (p.eval n)` at input length `n`: the length of the universal
quantifier block `r`. -/
noncomputable def seedPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  runsPoly p * p

/-- Polynomial giving `witnessLen (p.eval n)` at input length `n`: the length of the existential
quantifier block `u`. -/
noncomputable def witnessPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  runsPoly p * seedPoly p

@[simp]
theorem eval_runsPoly (p : Polynomial ℕ) (n : ℕ) : (runsPoly p).eval n = runs (p.eval n) := by
  simp [runsPoly, runs, halfRuns]

@[simp]
theorem eval_seedPoly (p : Polynomial ℕ) (n : ℕ) : (seedPoly p).eval n = seedLen (p.eval n) := by
  simp [seedPoly, seedLen]

@[simp]
theorem eval_witnessPoly (p : Polynomial ℕ) (n : ℕ) :
    (witnessPoly p).eval n = witnessLen (p.eval n) := by
  simp [witnessPoly, witnessLen, shifts]

private theorem halfRuns_eq (m : ℕ) : halfRuns m = 6 * (m + 7) + 6 := by
  unfold halfRuns
  omega

private theorem shifts_pos (m : ℕ) : 0 < shifts m := by
  unfold shifts runs halfRuns
  omega

private theorem shifts_le_two_pow (m : ℕ) : shifts m ≤ 2 ^ (m + 7) := by
  unfold shifts runs halfRuns
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.add_right_comm m 1 7, pow_succ]
    omega

private theorem two_pow_mul_eight_pow_halfRuns_lt (m : ℕ) :
    2 ^ (m + 7) * 8 ^ halfRuns m < 9 ^ halfRuns m := by
  rw [halfRuns_eq]
  exact Cslib.two_pow_mul_eight_pow_lt (m + 7)

private theorem two_pow_m_mul_eight_pow_halfRuns_lt (m : ℕ) :
    2 ^ m * 8 ^ halfRuns m < 9 ^ halfRuns m := by
  have hm : 2 ^ m ≤ 2 ^ (m + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (Nat.mul_le_mul_right _ hm).trans_lt (two_pow_mul_eight_pow_halfRuns_lt m)

private theorem shifts_mul_eight_pow_halfRuns_lt (m : ℕ) :
    shifts m * 8 ^ halfRuns m < 9 ^ halfRuns m :=
  (Nat.mul_le_mul_right _ (shifts_le_two_pow m)).trans_lt (two_pow_mul_eight_pow_halfRuns_lt m)

/-! ### Combinatorial shift-cover and soundness on amplified seeds -/

/-- An amplified seed for single-trial seed length `m`: `runs m` blocks of `m` bits each. Seeds
form an additive group under pointwise bit-string addition (xor). -/
abbrev Seed (m : ℕ) : Type := Fin (runs m) → BitString m

/-- The amplified test accepts `ω : Seed m` when a strict majority (`> halfRuns m`) of the
`runs m = 2 * halfRuns m` blocks satisfy the single-trial predicate `P`. -/
def majorityAccepts {m : ℕ} (P : (Fin m → Bool) → Bool) (ω : Seed m) : Prop :=
  halfRuns m < (univ.filter fun j : Fin (runs m) => P (ω j) = true).card

instance {m : ℕ} (P : (Fin m → Bool) → Bool) : DecidablePred (majorityAccepts P) :=
  fun _ => inferInstanceAs (Decidable (_ < _))

private theorem card_seed_eq (m : ℕ) : Fintype.card (Seed m) = (2 ^ m) ^ runs m := by
  simp [Seed, Fintype.card_fin, Fintype.card_bool]

/-- If at least two thirds of the single-trial seeds lie in `G`, then at most an
`(8 / 9) ^ halfRuns m` fraction of the amplified seeds have at most `halfRuns m` blocks in `G`:
the majority-vote bound `Cslib.card_filter_card_filter_le_le` on `Seed m`. -/
private theorem nine_pow_mul_card_filter_le {m : ℕ} {G : Finset (Fin m → Bool)}
    (hG : 2 * 2 ^ m ≤ 3 * G.card) :
    9 ^ halfRuns m *
        (univ.filter fun ω : Seed m => (univ.filter fun j => ω j ∈ G).card ≤ halfRuns m).card ≤
      8 ^ halfRuns m * Fintype.card (Seed m) := by
  have hcard : Fintype.card (Seed m) = Fintype.card (Fin m → Bool) ^ (2 * halfRuns m) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    rfl
  rw [hcard]
  exact Cslib.card_filter_card_filter_le_le G
    (by simpa [Fintype.card_fin, Fintype.card_bool] using hG) (halfRuns m)

/-- **Completeness on amplified seeds.** If at least two thirds of the single-trial seeds satisfy
`P s = true`, then there exist `shifts m` shift vectors covering every amplified seed `r : Seed m`
under `majorityAccepts P`: Lautemann's covering lemma
`Cslib.exists_forall_exists_add_mem_of_card_mul_card_compl_pow_lt` on the group `Seed m`. -/
theorem exists_shifts_majorityAccepts {m : ℕ} {P : (Fin m → Bool) → Bool}
    (hP : 2 * 2 ^ m ≤ 3 * (univ.filter fun s : Fin m → Bool => P s = true).card) :
    ∃ tests : Fin (shifts m) → Seed m, ∀ r : Seed m, ∃ i,
      majorityAccepts P (r + tests i) := by
  set S : Finset (Seed m) := univ.filter fun ω => majorityAccepts P ω with hSdef
  set N := Fintype.card (Seed m) with hNdef
  have hS : 9 ^ halfRuns m * #Sᶜ ≤ 8 ^ halfRuns m * N := by
    refine (nine_pow_mul_card_filter_le hP).trans_eq' (congrArg (9 ^ halfRuns m * ·) ?_)
    rw [hSdef, compl_filter]
    congr 1
    ext ω
    simp [majorityAccepts, not_lt]
  have hN : N * 8 ^ (halfRuns m * shifts m) < 9 ^ (halfRuns m * shifts m) := by
    rw [hNdef, card_seed_eq, pow_mul, pow_mul]
    change (2 ^ m) ^ shifts m * (8 ^ halfRuns m) ^ shifts m < (9 ^ halfRuns m) ^ shifts m
    rw [← mul_pow]
    exact Nat.pow_lt_pow_left (two_pow_m_mul_eight_pow_halfRuns_lt m) (shifts_pos m).ne'
  obtain ⟨tests, htests⟩ :=
    Cslib.exists_forall_exists_add_mem_of_card_mul_card_compl_pow_lt S (k := shifts m)
      (Nat.lt_of_mul_lt_mul_left (a := 9 ^ (halfRuns m * shifts m)) <| by
        calc 9 ^ (halfRuns m * shifts m) * (N * #Sᶜ ^ shifts m)
            = N * (9 ^ halfRuns m * #Sᶜ) ^ shifts m := by ring
          _ ≤ N * (8 ^ halfRuns m * N) ^ shifts m := by gcongr
          _ = N * 8 ^ (halfRuns m * shifts m) * N ^ shifts m := by ring
          _ < 9 ^ (halfRuns m * shifts m) * N ^ shifts m :=
            Nat.mul_lt_mul_of_pos_right hN (pow_pos Fintype.card_pos _))
  exact ⟨tests, fun r => (htests r).imp fun i hi => (mem_filter.1 hi).2⟩

/-- **Soundness on amplified seeds.** If at least two thirds of the single-trial seeds satisfy
`P s = false`, then for every tuple `tests : Fin (shifts m) → Seed m` of shift vectors, some
amplified seed `r : Seed m` fails `majorityAccepts P (r + tests i)` for all `i`: the converse
`Cslib.exists_forall_add_notMem_of_mul_card_lt` of Lautemann's covering lemma on `Seed m`. -/
theorem exists_seed_not_majorityAccepts {m : ℕ} {P : (Fin m → Bool) → Bool}
    (hP : 2 * 2 ^ m ≤ 3 * (univ.filter fun s : Fin m → Bool => P s = false).card)
    (tests : Fin (shifts m) → Seed m) :
    ∃ r : Seed m, ∀ i, ¬ majorityAccepts P (r + tests i) := by
  set G₀ : Finset (Fin m → Bool) := univ.filter fun s => P s = false with hG₀
  set S : Finset (Seed m) := univ.filter fun ω => majorityAccepts P ω with hSdef
  have hsub : S ⊆
      univ.filter fun ω : Seed m => (univ.filter fun j => ω j ∈ G₀).card ≤ halfRuns m := by
    intro ω hω
    have hω' : halfRuns m < (univ.filter fun j : Fin (runs m) => P (ω j) = true).card :=
      (mem_filter.1 hω).2
    refine mem_filter.2 ⟨mem_univ ω, ?_⟩
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin (runs m)))) (fun j => ω j ∈ G₀)
    rw [Finset.card_univ, Fintype.card_fin] at hpart
    have hruns : runs m = 2 * halfRuns m := rfl
    have hnot : (univ.filter fun j : Fin (runs m) => ω j ∉ G₀) =
        univ.filter fun j : Fin (runs m) => P (ω j) = true := by
      ext j
      simp [hG₀]
    rw [hnot] at hpart
    omega
  have hS : 9 ^ halfRuns m * #S ≤ 8 ^ halfRuns m * Fintype.card (Seed m) :=
    (Nat.mul_le_mul_left _ (card_le_card hsub)).trans (nine_pow_mul_card_filter_le hP)
  have hlt : shifts m * #S < Fintype.card (Seed m) := by
    refine Nat.lt_of_mul_lt_mul_left (a := 9 ^ halfRuns m) ?_
    calc 9 ^ halfRuns m * (shifts m * #S) = shifts m * (9 ^ halfRuns m * #S) := by ring
      _ ≤ shifts m * (8 ^ halfRuns m * Fintype.card (Seed m)) := Nat.mul_le_mul_left _ hS
      _ = shifts m * 8 ^ halfRuns m * Fintype.card (Seed m) := by ring
      _ < 9 ^ halfRuns m * Fintype.card (Seed m) :=
        Nat.mul_lt_mul_of_pos_right (shifts_mul_eight_pow_halfRuns_lt m) Fintype.card_pos
  obtain ⟨r, hr⟩ := Cslib.exists_forall_add_notMem_of_mul_card_lt S hlt tests
  exact ⟨r, fun i hi => hr i (mem_filter.2 ⟨mem_univ _, hi⟩)⟩

/-! ### Bit-string encoding and decoding of seeds and shift tables -/

/-- Decode a flat bit string `r` into an amplified seed, reading `r` as `runs m` consecutive
blocks of `m` bits: bit `k` of block `j` is bit `j * m + k` of `r`, and bits missing from a short
`r` read as `false` (`Cslib.BitString.ofList`, `Cslib.BitString.block`). -/
def listToSeed (m : ℕ) (r : List Bool) : Seed m :=
  BitString.block (BitString.ofList (runs m * m) r)

/-- Decode a flat bit string `u` into a table of `shifts m` shift vectors, reading `u` as
`shifts m` consecutive blocks of `seedLen m` bits, each an amplified seed as in `listToSeed`: bit
`k` of block `j` of shift `i` is bit `i * seedLen m + j * m + k` of `u`, and bits missing from a
short `u` read as `false`. -/
def listToShifts (m : ℕ) (u : List Bool) : Fin (shifts m) → Seed m :=
  fun i => BitString.block (BitString.block (BitString.ofList (shifts m * (runs m * m)) u) i)

/-- Encode an amplified seed `ω : Seed m` as a flat bit string of length `seedLen m`, inverting
`listToSeed`. -/
def seedToList {m : ℕ} (ω : Seed m) : List Bool :=
  List.ofFn (BitString.blocksEquiv.symm ω)

/-- Encode a table of shift vectors `tests : Fin (shifts m) → Seed m` as a flat bit string of
length `witnessLen m`, inverting `listToShifts`. -/
def shiftsToList {m : ℕ} (tests : Fin (shifts m) → Seed m) : List Bool :=
  List.ofFn (BitString.blocksEquiv.symm fun i => BitString.blocksEquiv.symm (tests i))

@[simp]
theorem length_seedToList {m : ℕ} (ω : Seed m) : (seedToList ω).length = seedLen m := by
  simp [seedToList, seedLen]

@[simp]
theorem length_shiftsToList {m : ℕ} (tests : Fin (shifts m) → Seed m) :
    (shiftsToList tests).length = witnessLen m := by
  simp [shiftsToList, witnessLen, seedLen]

@[simp]
theorem listToSeed_seedToList {m : ℕ} (ω : Seed m) : listToSeed m (seedToList ω) = ω := by
  simp only [listToSeed, seedToList, BitString.ofList_ofFn, ← BitString.blocksEquiv_apply,
    Equiv.apply_symm_apply]

@[simp]
theorem listToShifts_shiftsToList {m : ℕ} (tests : Fin (shifts m) → Seed m) :
    listToShifts m (shiftsToList tests) = tests := by
  funext i
  simp only [listToShifts, shiftsToList, BitString.ofList_ofFn, ← BitString.blocksEquiv_apply,
    Equiv.apply_symm_apply]

/-! ### The functional matrix verifier and its polynomial-time certificate -/

variable {α : Type}

/-- The `j`-th trial seed of length `m` under the `i`-th shift of a combined certificate
`w = u ++ r`, where `u` lists `shifts m` shift vectors of `seedLen m` bits and `r` is the
amplified seed: the bitwise xor of the rows of width `m` numbered `shifts m * runs m + j` (block
`j` of `r`) and `i * runs m + j` (block `j` of the `i`-th shift) of `w`
(`Cslib.BitString.listRow`). Bits missing from a short `w` read as `false`, and extra bits of `w`
are ignored. -/
def trialSeed (m : ℕ) (w : List Bool) (i j : ℕ) : List Bool :=
  List.zipWith Bool.xor (BitString.listRow m (shifts m * runs m + j) w)
    (BitString.listRow m (i * runs m + j) w)

/-- Whether the `i`-th shift vector causes a strict majority (`> halfRuns m`) of the `runs m`
trials to be accepted by `V`. -/
def shiftAccepts (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (a : α) (w : List Bool) (i : ℕ) : Bool :=
  let m := p.eval (enc a).length
  decide (halfRuns m < (List.range (runs m)).countP fun j => V (a, trialSeed m w i j))

/-- The Sipser–Lautemann `Σ₂` matrix verifier: given `(a, w)` where `w = u ++ r` consists of an
existential shift-table certificate `u` of length `witnessLen m` and a universal seed `r` of length
`seedLen m` (for `m = p.eval (enc a).length`), test whether some shift `i < shifts m` makes a
strict majority of the `runs m` shifted trials accept. The verifier is total: bits missing from a
short `w` read as `false` and extra bits of `w` are ignored (`trialSeed`). -/
def verifier (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  let m := p.eval (enc x.1).length
  (List.range (shifts m)).any fun i => shiftAccepts enc p V x.1 x.2 i

/-- If `V` is computable in polynomial time, then so is the Sipser–Lautemann matrix verifier
`verifier enc p V`. -/
@[fun_prop]
theorem verifier_polyTime {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (verifier enc p V) (encPair enc encBits) encBool := by
  unfold verifier
  apply ComputableInPolyTime.anyWithInput (encA := encUnary)
  · unfold shifts runs halfRuns
    fun_prop
  · unfold shiftAccepts
    apply ComputableInPolyTime.unary_lt'
    · unfold halfRuns
      fun_prop
    · apply ComputableInPolyTime.countPWithInput (encA := encUnary)
      · unfold runs halfRuns
        fun_prop
      · unfold trialSeed shifts runs halfRuns
        fun_prop

/-! ### Correctness of the matrix verifier -/

/-- On a combined certificate `u ++ r` with `u.length = witnessLen m`, `trialSeed` reconstructs
the `j`-th block of the shifted seed `listToSeed m r + listToShifts m u i`. -/
private theorem trialSeed_append {m : ℕ} {u r : List Bool} (hu : u.length = witnessLen m)
    (i : Fin (shifts m)) (j : Fin (runs m)) :
    trialSeed m (u ++ r) i.1 j.1 = List.ofFn ((listToSeed m r + listToShifts m u i) j) := by
  apply List.ext_getElem (by simp [trialSeed])
  intro k hk _
  simp only [trialSeed, List.length_zipWith, BitString.length_listRow, min_self] at hk
  have hidx : (i.1 * runs m + j.1) * m + k = k + m * j.1 + runs m * m * i.1 := by ring
  have hlt : (i.1 * runs m + j.1) * m + k < u.length := by
    rw [hu, hidx]
    exact (finProdFinEquiv (i, finProdFinEquiv (j, ⟨k, hk⟩))).2
  have hsplit : (shifts m * runs m + j.1) * m + k = u.length + (k + m * j.1) := by
    rw [hu, witnessLen, seedLen]
    ring
  have hleft : (BitString.listRow m (shifts m * runs m + j.1) (u ++ r))[k]'(by simpa using hk) =
      r.getD (k + m * j.1) false := by
    rw [BitString.getElem_listRow hk, hsplit, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  have hright : (BitString.listRow m (i.1 * runs m + j.1) (u ++ r))[k]'(by simpa using hk) =
      u.getD (k + m * j.1 + runs m * m * i.1) false := by
    rw [BitString.getElem_listRow hk, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hlt, hidx]
  simp only [trialSeed, List.getElem_zipWith, hleft, hright, List.getElem_ofFn, Pi.add_apply,
    Bool.add_eq_xor, listToSeed, listToShifts, BitString.block_apply, BitString.ofList,
    finProdFinEquiv_apply_val]

/-- On a combined certificate `u ++ r` with `u.length = witnessLen (p.eval (enc a).length)`,
`shiftAccepts` agrees with `majorityAccepts` on the `i`-th shifted seed. -/
theorem shiftAccepts_append_iff {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {u r : List Bool}
    (hu : u.length = witnessLen (p.eval (enc a).length))
    (i : Fin (shifts (p.eval (enc a).length))) :
    shiftAccepts enc p V a (u ++ r) i.1 = true ↔
      majorityAccepts (fun s => V (a, List.ofFn s))
        (listToSeed (p.eval (enc a).length) r + listToShifts (p.eval (enc a).length) u i) := by
  unfold shiftAccepts majorityAccepts
  dsimp only
  rw [decide_eq_true_iff, List.countP_range_eq_card_filter]
  refine Iff.of_eq (congrArg (halfRuns (p.eval (enc a).length) < ·) (congrArg Finset.card ?_))
  ext j
  simp only [mem_filter, mem_univ, true_and, trialSeed_append hu i j]

/-- On a combined certificate `u ++ r` with `u.length = witnessLen (p.eval (enc a).length)`,
`verifier enc p V (a, u ++ r)` accepts iff some shift `i` satisfies `majorityAccepts`. -/
theorem verifier_append_iff {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {u r : List Bool}
    (hu : u.length = witnessLen (p.eval (enc a).length)) :
    verifier enc p V (a, u ++ r) = true ↔
      ∃ i : Fin (shifts (p.eval (enc a).length)),
        majorityAccepts (fun s => V (a, List.ofFn s))
          (listToSeed (p.eval (enc a).length) r + listToShifts (p.eval (enc a).length) u i) := by
  unfold verifier
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, hacc⟩
    exact ⟨⟨i, hi⟩, (shiftAccepts_append_iff hu ⟨i, hi⟩).1 hacc⟩
  · rintro ⟨i, hacc⟩
    exact ⟨i.1, i.2, (shiftAccepts_append_iff hu i).2 hacc⟩

/-- If `V` decides `A` with bounded error using seed polynomial `p`, then `verifier enc p V` is a
valid `Σ₂` alternating verifier for `A` with quantifier block lengths
`[witnessPoly p, seedPoly p]`. -/
theorem isAlternatingVerifier_verifier {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (hA : DecidesWithBoundedError enc p V A) :
    IsAlternatingVerifier enc true [witnessPoly p, seedPoly p] (verifier enc p V) A := by
  intro a
  set m := p.eval (enc a).length
  simp only [List.map_cons, List.map_nil, eval_witnessPoly, eval_seedPoly,
    alternation_true_cons, alternation_false_cons, alternation_nil, List.append_nil]
  constructor
  · intro ha
    obtain ⟨tests, hcover⟩ := exists_shifts_majorityAccepts ((hA a).1 ha)
    refine ⟨shiftsToList tests, length_shiftsToList tests, fun r _ => ?_⟩
    rw [verifier_append_iff (length_shiftsToList tests), listToShifts_shiftsToList]
    exact hcover (listToSeed m r)
  · rintro ⟨u, hu, hforall⟩
    by_contra hna
    obtain ⟨ω, hω⟩ := exists_seed_not_majorityAccepts ((hA a).2 hna) (listToShifts m u)
    have hacc := hforall (seedToList ω) (length_seedToList ω)
    rw [verifier_append_iff hu, listToSeed_seedToList] at hacc
    obtain ⟨i, hi⟩ := hacc
    exact hω i hi

end SipserLautemann

/-! ### Main class inclusions -/

variable {α : Type} {enc : α ↪ List Bool}

/-- **The Sipser–Gács–Lautemann theorem (`Σ₂` form)** [Sipser][Sipser1983],
[Lautemann][Lautemann1983], [Arora and Barak, Theorem 7.15][AroraBarak09]: every problem in `BPP`
lies in `Σ₂`. -/
theorem BPP_subset_SigmaP_two : BPP enc ⊆ SigmaP 2 enc := by
  rintro A ⟨p, V, hV, hA⟩
  exact ⟨[SipserLautemann.witnessPoly p, SipserLautemann.seedPoly p],
    SipserLautemann.verifier enc p V, rfl,
    (SipserLautemann.verifier_polyTime hV),
    SipserLautemann.isAlternatingVerifier_verifier hA⟩

/-- **The Sipser–Gács–Lautemann theorem (`Π₂` form)**: every problem in `BPP` lies in `Π₂`,
obtained from `BPP_subset_SigmaP_two` by complement closure of `BPP` and quantifier duality. -/
theorem BPP_subset_PiP_two : BPP enc ⊆ PiP 2 enc := fun A hA => by
  simpa using compl_mem_PiP_of_mem_SigmaP (BPP_subset_SigmaP_two (compl_mem_BPP hA))

/-- **The Sipser–Gács–Lautemann theorem**: `BPP ⊆ Σ₂ ∩ Π₂` [Sipser][Sipser1983],
[Lautemann][Lautemann1983], [Arora and Barak, Theorem 7.15][AroraBarak09]. -/
theorem BPP_subset_SigmaP_two_inter_PiP_two : BPP enc ⊆ SigmaP 2 enc ∩ PiP 2 enc :=
  Set.subset_inter BPP_subset_SigmaP_two BPP_subset_PiP_two

/-- Every problem in `BPP` lies in the polynomial hierarchy `PH`. -/
theorem BPP_subset_PH : BPP enc ⊆ PH enc :=
  BPP_subset_SigmaP_two.trans (SigmaP_subset_PH 2)

end Cslib.Complexity
