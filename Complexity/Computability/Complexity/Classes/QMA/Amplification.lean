/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.QMA
public import Complexity.Computability.Complexity.Classes.BQP.Amplification
public import Complexity.Foundations.Data.BitString.Block
public import Complexity.Foundations.Quantum.TensorPower
import Complexity.Foundations.Combinatorics.MajorityVote.Weighted
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Weak error reduction for `QMA`

The completeness `2 / 3` and soundness `1 / 3` in the definition of `QMA` (`Cslib.Complexity.QMA`)
can be made exponentially close to `1` and `0`: `A ∈ QMA enc` exactly when for every polynomial `q`
the problem has verifiers with completeness `1 - 2^{-q(n)}` and soundness `2^{-q(n)}`, where `n` is
the length of the encoded instance (`Cslib.Complexity.mem_QMA_iff_forall_errorExponent`). This is
Kitaev's parallel repetition [Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002], Section 14.2;
[Marriott, Watrous][MarriottWatrous2005], Theorem 3.2, here at the gap `(2 / 3, 1 / 3)`. The witness
grows with the number of repetitions, which [Watrous][Watrous2008], Section V.3, calls *weak* error
reduction.

The amplified verifier family (`Cslib.Quantum.UniformVerifierFamily.amplify`) reuses the reversible
majority vote of the error reduction for `BQP` (`Cslib.Quantum.Amplify`). On inputs of length `n`,
for a verifier of width `m` and witness length `p`, the amplified witness consists of `2 r` blocks
of `p` qubits, and the register consists of `2 r + 1` blocks of width `W = m + 2 r p` and the
counter's ancillas. Block `0` holds the input and the witness blocks; block `j + 1` is copy `j` of
the original register. The amplified circuit (`Cslib.Quantum.QMAAmplify.codes`):

1. moves witness block `j` into the witness qubits of copy `j` with CNOT gates
   (`Cslib.Quantum.QMAAmplify.moveInCodes`, `Cslib.Quantum.QMAAmplify.moveOutCodes`);
2. copies the input into each copy (`Cslib.Quantum.Amplify.copyCodes`);
3. runs the original circuit on each copy (`Cslib.Quantum.Amplify.copiesCodes`);
4. computes the strict majority of the copies' answers into qubit `0` with a reversible counter.

Steps 1, 2 and 4 are classical, so the acceptance probability is the weight of the outcomes with
more than `r` accepting copies under the `2 r`-fold tensor power of the original circuit applied to
the witness (`Cslib.Quantum.UniformVerifierFamily.acceptProb_amplify`).

* **Completeness.** On the product witness `ψ^{⊗ 2 r}` the copies are independent, and the
  majority-vote bound `Cslib.sum_prod_le_of_card_filter_le` gives acceptance probability at least
  `1 - (8 / 9) ^ r` (`Cslib.Quantum.UniformVerifierFamily.exists_one_sub_le_acceptProb_amplify`).
* **Soundness.** The witness may be entangled across the blocks. The original verifier accepts every
  witness with probability at most `1 / 3` of its squared norm, so each copy accepts with
  probability at most `1 / 3` conditioned on the outcomes of the others
  (`Cslib.Quantum.sum_filter_mul_norm_tensorPowerApply_le`). The resulting exponential-moment bound
  gives acceptance probability at most `(8 / 9) ^ r`
  (`Cslib.Quantum.UniformVerifierFamily.acceptProb_amplify_le`).

Taking `r = 6 q` gives the error `2^{-q}`.

## Main definitions

* `Cslib.Quantum.QMAAmplify.codes`: the gate codes of the amplified verifier.
* `Cslib.Quantum.UniformVerifierFamily.amplify`: the amplified verifier family.

## Main results

* `Cslib.Quantum.UniformVerifierFamily.acceptProb_amplify`: the acceptance probability of the
  amplified family.
* `Cslib.Quantum.UniformVerifierFamily.acceptProb_amplify_le`,
  `Cslib.Quantum.UniformVerifierFamily.exists_one_sub_le_acceptProb_amplify`: amplified soundness
  and completeness.
* `Cslib.Complexity.PromiseQMA_subset_errorExponent`: `QMA(2 / 3, 1 / 3) ⊆ QMA(1 - 2^{-q}, 2^{-q})`.
* `Cslib.Complexity.mem_QMA_iff_forall_errorExponent`: error reduction for `QMA`.

Error reduction from an arbitrary inverse-polynomial gap, as in [Marriott, Watrous]
[MarriottWatrous2005], Theorem 3.2, and strong error reduction, which keeps the witness length
([Marriott, Watrous][MarriottWatrous2005], Theorem 3.3), are not formalized here.

## References

* [A. Kitaev, A. Shen, M. Vyalyi, *Classical and Quantum Computation*][KitaevShenVyalyi2002]
* [C. Marriott, J. Watrous, *Quantum Arthur–Merlin games*][MarriottWatrous2005]
* [J. Watrous, *Quantum computational complexity*][Watrous2008]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset GateCode Turing.MultiTapeTM

namespace QMAAmplify

/-- Division with remainder by `W` is unique. -/
private theorem eq_of_add_mul_eq {W a a' b b' : ℕ} (ha : a < W) (ha' : a' < W)
    (h : a + b * W = a' + b' * W) : a = a' ∧ b = b' := by
  have hW : 0 < W := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  have hmod := congrArg (· % W) h
  have hdiv := congrArg (· / W) h
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hmod
  simp only [Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt ha'] at hdiv
  exact ⟨hmod, by omega⟩

/-- CNOT gates copying witness block `j < k` (qubits `n + p j, …`) into the witness qubits of copy
`j` (qubits `n + (j + 1) W, …`). -/
def moveInCodes (n p W k : ℕ) : List GateCode :=
  (List.range k).flatMap fun j => (List.range p).map fun i =>
    (false, i + n + (j + 1) * W, [i + p * j + n])

/-- CNOT gates clearing the witness blocks, after `moveInCodes`. -/
def moveOutCodes (n p W k : ℕ) : List GateCode :=
  (List.range k).flatMap fun j => (List.range p).map fun i =>
    (false, i + p * j + n, [i + n + (j + 1) * W])

/-- The gates of `moveInCodes`. -/
theorem mem_moveInCodes {n p W k : ℕ} {g : GateCode} :
    g ∈ moveInCodes n p W k ↔
      ∃ j < k, ∃ i < p, g = (false, i + n + (j + 1) * W, [i + p * j + n]) := by
  simp only [moveInCodes, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨j, hj, i, hi, rfl⟩
    exact ⟨j, hj, i, hi, rfl⟩
  · rintro ⟨j, hj, i, hi, rfl⟩
    exact ⟨j, hj, i, hi, rfl⟩

/-- The gates of `moveOutCodes`. -/
theorem mem_moveOutCodes {n p W k : ℕ} {g : GateCode} :
    g ∈ moveOutCodes n p W k ↔
      ∃ j < k, ∃ i < p, g = (false, i + p * j + n, [i + n + (j + 1) * W]) := by
  simp only [moveOutCodes, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨j, hj, i, hi, rfl⟩
    exact ⟨j, hj, i, hi, rfl⟩
  · rintro ⟨j, hj, i, hi, rfl⟩
    exact ⟨j, hj, i, hi, rfl⟩

/-- Qubit `i` of block `j < k` of width `p` lies in the first `k p` qubits. -/
private theorem add_mul_lt {p k i j : ℕ} (hj : j < k) (hi : i < p) : i + p * j < k * p := by
  have := Nat.mul_le_mul_left p (show j + 1 ≤ k by omega)
  rw [Nat.mul_add, Nat.mul_one] at this
  rw [Nat.mul_comm k]
  omega

/-- Block `j + 1` of width `W` starts at or after qubit `W`. -/
private theorem le_add_mul {W i j : ℕ} : W ≤ i + (j + 1) * W := by
  have := Nat.le_mul_of_pos_left W (show 0 < j + 1 by omega)
  omega

/-- The gates of `moveInCodes` have distinct targets. -/
theorem nodup_moveInCodes {n p W k : ℕ} (hW : n + p ≤ W) :
    ((moveInCodes n p W k).map fun g => g.2.1).Nodup := by
  simp only [moveInCodes, List.map_flatMap, List.map_map, Function.comp_def]
  refine List.nodup_flatMap.mpr ⟨fun j _ => (List.nodup_range).map fun i i' h => by
    simpa using h, ?_⟩
  refine (List.nodup_range).pairwise_of_forall_ne fun j _ j' _ hjj' => ?_
  simp only [List.Disjoint, List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩ ⟨i', hi', h⟩
  have h' := eq_of_add_mul_eq (W := W) (a := i' + n) (a' := i + n) (b := j' + 1) (b' := j + 1)
    (by omega) (by omega) (by omega)
  omega

/-- The gates of `moveOutCodes` have distinct targets. -/
theorem nodup_moveOutCodes {n p W k : ℕ} :
    ((moveOutCodes n p W k).map fun g => g.2.1).Nodup := by
  simp only [moveOutCodes, List.map_flatMap, List.map_map, Function.comp_def]
  refine List.nodup_flatMap.mpr ⟨fun j _ => (List.nodup_range).map fun i i' h => by
    simpa using h, ?_⟩
  refine (List.nodup_range).pairwise_of_forall_ne fun j _ j' _ hjj' => ?_
  simp only [List.Disjoint, List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩ ⟨i', hi', h⟩
  have h' : i' + j' * p = i + j * p := by rw [Nat.mul_comm j', Nat.mul_comm j]; omega
  have := eq_of_add_mul_eq hi' hi h'
  omega

/-- No gate of `moveInCodes` reads the target of another: the targets lie in the copies and the
controls in the witness blocks. -/
private theorem moveInCodes_read {n p W k : ℕ} (hW : n + k * p ≤ W) :
    ∀ g ∈ moveInCodes n p W k, ∀ g' ∈ moveInCodes n p W k, g.2.1 ∉ g'.2.2 := by
  intro g hg g' hg'
  obtain ⟨j, hj, i, hi, rfl⟩ := mem_moveInCodes.mp hg
  obtain ⟨j', hj', i', hi', rfl⟩ := mem_moveInCodes.mp hg'
  have := add_mul_lt hj' hi'
  have := le_add_mul (W := W) (i := i + n) (j := j)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- No gate of `moveOutCodes` reads the target of another: the targets lie in the witness blocks
and the controls in the copies. -/
private theorem moveOutCodes_read {n p W k : ℕ} (hW : n + k * p ≤ W) :
    ∀ g ∈ moveOutCodes n p W k, ∀ g' ∈ moveOutCodes n p W k, g.2.1 ∉ g'.2.2 := by
  intro g hg g' hg'
  obtain ⟨j, hj, i, hi, rfl⟩ := mem_moveOutCodes.mp hg
  obtain ⟨j', hj', i', hi', rfl⟩ := mem_moveOutCodes.mp hg'
  have := add_mul_lt hj hi
  have := le_add_mul (W := W) (i := i' + n) (j := j')
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- `moveInCodes` adds witness qubit `i` of block `j` to qubit `i` of the witness of copy `j`. -/
private theorem readBit_classicalRun_moveInCodes {n p W k N : ℕ} (hW : n + k * p ≤ W)
    (hN : ∀ j < k, ∀ i < p, i + n + (j + 1) * W < N) (Y : Fin N → Bool) {j i : ℕ} (hj : j < k)
    (hi : i < p) :
    readBit (classicalRun (moveInCodes n p W k) Y) (i + n + (j + 1) * W) =
      (readBit Y (i + n + (j + 1) * W) ^^ readBit Y (i + p * j + n)) := by
  have hpW : n + p ≤ W := by
    have := Nat.le_mul_of_pos_left p (show 0 < k by omega)
    omega
  have := readBit_classicalRun_of_mem (fun g hg => by
      obtain ⟨j, hj, i, hi, rfl⟩ := mem_moveInCodes.mp hg
      exact hN j hj i hi) (nodup_moveInCodes hpW) (moveInCodes_read hW) Y
      (mem_moveInCodes.mpr ⟨j, hj, i, hi, rfl⟩)
  simpa only [List.all_cons, List.all_nil, Bool.and_true] using this

/-- `moveOutCodes` adds qubit `i` of the witness of copy `j` to witness qubit `i` of block `j`. -/
private theorem readBit_classicalRun_moveOutCodes {n p W k N : ℕ} (hW : n + k * p ≤ W)
    (hWN : W ≤ N) (Y : Fin N → Bool) {j i : ℕ} (hj : j < k) (hi : i < p) :
    readBit (classicalRun (moveOutCodes n p W k) Y) (i + p * j + n) =
      (readBit Y (i + p * j + n) ^^ readBit Y (i + n + (j + 1) * W)) := by
  have := readBit_classicalRun_of_mem (fun g hg => by
      obtain ⟨j, hj, i, hi, rfl⟩ := mem_moveOutCodes.mp hg
      have := add_mul_lt hj hi
      dsimp only
      omega) nodup_moveOutCodes (moveOutCodes_read hW) Y
      (mem_moveOutCodes.mpr ⟨j, hj, i, hi, rfl⟩)
  simpa only [List.all_cons, List.all_nil, Bool.and_true] using this

/-- `moveInCodes` changes only the witness qubits of the copies. -/
private theorem readBit_classicalRun_moveInCodes_of_ne {n p W k N c : ℕ}
    (hc : ∀ j < k, ∀ i < p, i + n + (j + 1) * W ≠ c) (Y : Fin N → Bool) :
    readBit (classicalRun (moveInCodes n p W k) Y) c = readBit Y c :=
  readBit_classicalRun_of_forall_ne (fun g hg => by
    obtain ⟨j, hj, i, hi, rfl⟩ := mem_moveInCodes.mp hg
    exact hc j hj i hi) Y

/-- `moveOutCodes` changes only the witness blocks. -/
private theorem readBit_classicalRun_moveOutCodes_of_ne {n p W k N c : ℕ}
    (hc : ∀ j < k, ∀ i < p, i + p * j + n ≠ c) (Y : Fin N → Bool) :
    readBit (classicalRun (moveOutCodes n p W k) Y) c = readBit Y c :=
  readBit_classicalRun_of_forall_ne (fun g hg => by
    obtain ⟨j, hj, i, hi, rfl⟩ := mem_moveOutCodes.mp hg
    exact hc j hj i hi) Y

/-! ### The registers of the amplified verifier -/

variable {n m p W R : ℕ}

/-- Copy `j` of the original register, in block `j + 1` of the amplified register. -/
def copyEmb (hm : m ≤ W) (j : Fin (2 * R)) : Fin m ↪ Fin (Amplify.width W (2 * R) R) :=
  blockEmb ((j + 1) * W)
    (by have := Amplify.block_le_width (w := W) (k := 2 * R) (t := R) j.2; omega)

@[simp] theorem copyEmb_apply_val (hm : m ≤ W) (j : Fin (2 * R)) (i : Fin m) :
    (copyEmb hm j i : ℕ) = i + (j + 1) * W := rfl

/-- All copies of the original register. -/
def copiesEmb (hm : m ≤ W) : Fin (2 * R) × Fin m ↪ Fin (Amplify.width W (2 * R) R) where
  toFun q := copyEmb hm q.1 q.2
  inj' q q' h := by
    have h' : (q.2 : ℕ) + (q.1 + 1) * W = q'.2 + (q'.1 + 1) * W := congrArg Fin.val h
    have := eq_of_add_mul_eq (lt_of_lt_of_le q.2.2 hm) (lt_of_lt_of_le q'.2.2 hm) h'
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext this.1)

@[simp] theorem copiesEmb_apply (hm : m ≤ W) (q : Fin (2 * R) × Fin m) :
    copiesEmb hm q = copyEmb hm q.1 q.2 := rfl

/-- The witness qubits `n, …, n + p - 1` of all copies, indexed by the copy and the qubit. -/
def slotEmb (hnp : n + p ≤ m) (hm : m ≤ W) :
    Fin (2 * R) × Fin p ↪ Fin (Amplify.width W (2 * R) R) :=
  (Function.Embedding.prodMap (Function.Embedding.refl _) (blockEmb n hnp)).trans (copiesEmb hm)

@[simp] theorem slotEmb_apply_val (hnp : n + p ≤ m) (hm : m ≤ W) (q : Fin (2 * R) × Fin p) :
    (slotEmb hnp hm q : ℕ) = q.2 + n + (q.1 + 1) * W := rfl

/-- The witness qubits of all copies, indexed as the witness blocks are. -/
def slotsEmb (hnp : n + p ≤ m) (hm : m ≤ W) : Fin (2 * R * p) ↪ Fin (Amplify.width W (2 * R) R) :=
  finProdFinEquiv.symm.toEmbedding.trans (slotEmb hnp hm)

/-- The witness qubit `i` of copy `j`. -/
theorem slotsEmb_finProdFinEquiv (hnp : n + p ≤ m) (hm : m ≤ W) (q : Fin (2 * R) × Fin p) :
    slotsEmb hnp hm (finProdFinEquiv q) = slotEmb hnp hm q := by
  simp [slotsEmb]

/-- The first block lies in the register. -/
theorem lt_width_of_lt {c : ℕ} (h : c < W) : c < Amplify.width W (2 * R) R :=
  lt_of_lt_of_le h
    (Amplify.le_base.trans (Amplify.base_lt_width (w := W) (k := 2 * R) (t := R)).le)

/-- The input and the witness blocks fit in the first block of the register. -/
theorem witBlock_le (hW : n + 2 * R * p ≤ W) : n + 2 * R * p ≤ Amplify.width W (2 * R) R :=
  hW.trans (Amplify.le_base.trans (Amplify.base_lt_width (w := W) (k := 2 * R) (t := R)).le)

/-- **Moving the witness blocks into the copies**: the CNOT gates of `moveInCodes` and then
`moveOutCodes` move the bits on the witness blocks `n, …, n + 2 R p - 1` into the witness qubits
of the copies, when the latter are zero. -/
theorem classicalRun_moveCodes (hnp : n + p ≤ m) (hm : m ≤ W) (hW : n + 2 * R * p ≤ W)
    (X : Fin (Amplify.width W (2 * R) R) → Bool) (hX : ∀ c, n ≤ c → readBit X c = false)
    (Z : Fin (2 * R * p) → Bool) :
    classicalRun (moveInCodes n p W (2 * R) ++ moveOutCodes n p W (2 * R))
        (glue (blockEmb n (witBlock_le hW)) Z X) = glue (slotsEmb hnp hm) Z X := by
  have hslotN {j i : ℕ} (hj : j < 2 * R) (hi : i < p) :
      i + n + (j + 1) * W < Amplify.width W (2 * R) R := by
    have := Amplify.block_le_width (w := W) (k := 2 * R) (t := R) hj
    omega
  have hwitW {j i : ℕ} (hj : j < 2 * R) (hi : i < p) : i + p * j + n < W := by
    have := add_mul_lt (k := 2 * R) hj hi
    omega
  have hWN : W ≤ Amplify.width W (2 * R) R :=
    Amplify.le_base.trans (Amplify.base_lt_width (w := W) (k := 2 * R) (t := R)).le
  -- the bits of the glued strings
  have hGwit {j i : ℕ} (hj : j < 2 * R) (hi : i < p) :
      readBit (glue (blockEmb n (witBlock_le hW)) Z X) (i + p * j + n) =
        Z (finProdFinEquiv (⟨j, hj⟩, ⟨i, hi⟩)) := by
    rw [readBit_of_lt _ (lt_width_of_lt (hwitW hj hi))]
    exact glue_apply_emb _ Z X (finProdFinEquiv (⟨j, hj⟩, ⟨i, hi⟩))
  have hGoff {c : ℕ} (hc : ∀ q : Fin (2 * R * p), (q : ℕ) + n ≠ c) :
      readBit (glue (blockEmb n (witBlock_le hW)) Z X) c = readBit X c :=
    readBit_glue_of_forall_ne _ Z X fun q h => hc q h
  have hSoff {c : ℕ} (hc : ∀ q : Fin (2 * R) × Fin p, (q.2 : ℕ) + n + (q.1 + 1) * W ≠ c) :
      readBit (glue (slotsEmb hnp hm) Z X) c = readBit X c := by
    refine readBit_glue_of_forall_ne _ Z X fun q h => ?_
    obtain ⟨q', rfl⟩ := finProdFinEquiv.surjective q
    rw [slotsEmb_finProdFinEquiv, slotEmb_apply_val] at h
    exact hc q' h
  -- after `moveInCodes`, the witness qubits of the copies hold the witness blocks
  have hIn {j i : ℕ} (hj : j < 2 * R) (hi : i < p) :
      readBit (classicalRun (moveInCodes n p W (2 * R)) (glue (blockEmb n (witBlock_le hW)) Z X))
        (i + n + (j + 1) * W) = Z (finProdFinEquiv (⟨j, hj⟩, ⟨i, hi⟩)) := by
    have hle := le_add_mul (W := W) (i := i + n) (j := j)
    rw [readBit_classicalRun_moveInCodes hW (fun _ hj _ hi => hslotN hj hi) _ hj hi, hGwit hj hi,
      hGoff fun q h => ?_, hX _ (by omega), Bool.false_xor]
    have := q.2
    omega
  refine funext_readBit fun c => ?_
  rw [classicalRun_append]
  -- the witness qubits of the copies
  by_cases hA : ∃ j < 2 * R, ∃ i < p, i + n + (j + 1) * W = c
  · obtain ⟨j, hj, i, hi, rfl⟩ := hA
    rw [readBit_classicalRun_moveOutCodes_of_ne (fun j' hj' i' hi' h => by
        have := hwitW hj' hi'
        have := le_add_mul (W := W) (i := i + n) (j := j)
        omega), hIn hj hi]
    have hlt := hslotN hj hi
    rw [readBit_of_lt _ hlt]
    have : (⟨i + n + (j + 1) * W, hlt⟩ : Fin (Amplify.width W (2 * R) R)) =
        slotsEmb hnp hm (finProdFinEquiv (⟨j, hj⟩, ⟨i, hi⟩)) := by
      rw [slotsEmb_finProdFinEquiv]
      rfl
    rw [this, glue_apply_emb]
  -- the witness blocks
  by_cases hB : ∃ j < 2 * R, ∃ i < p, i + p * j + n = c
  · obtain ⟨j, hj, i, hi, rfl⟩ := hB
    have hw := hwitW hj hi
    rw [readBit_classicalRun_moveOutCodes hW hWN _ hj hi, hIn hj hi,
      readBit_classicalRun_moveInCodes_of_ne (fun j' hj' i' hi' h => by
        have := le_add_mul (W := W) (i := i' + n) (j := j')
        omega), hGwit hj hi, Bool.xor_self, hSoff fun q h => ?_, hX _ (by omega)]
    have := le_add_mul (W := W) (i := (q.2 : ℕ) + n) (j := q.1)
    omega
  -- the other qubits are untouched
  push Not at hA hB
  rw [readBit_classicalRun_moveOutCodes_of_ne hB, readBit_classicalRun_moveInCodes_of_ne hA,
    hGoff fun q h => ?_, hSoff fun q h => hA q.1 q.1.2 q.2 q.2.2 h]
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective q
  exact hB j j.2 i i.2 h

/-- Moving the witness blocks is classical. -/
theorem isClassical_moveCodes (hW : n + 2 * R * p ≤ W) :
    IsClassical (Amplify.width W (2 * R) R)
      (moveInCodes n p W (2 * R) ++ moveOutCodes n p W (2 * R)) := by
  refine IsClassical.append.mpr ⟨fun g hg => ?_, fun g hg => ?_⟩
  on_goal 1 => obtain ⟨j, hj, i, hi, rfl⟩ := mem_moveInCodes.mp hg
  on_goal 2 => obtain ⟨j, hj, i, hi, rfl⟩ := mem_moveOutCodes.mp hg
  -- both kinds of gates are CNOTs between a witness qubit and a qubit of a copy
  all_goals
    have := add_mul_lt (k := 2 * R) hj hi
    have := Amplify.block_le_width (w := W) (k := 2 * R) (t := R) hj
    have := le_add_mul (W := W) (i := i + n) (j := j)
    have := lt_width_of_lt (R := R) (show i + p * j + n < W by omega)
    refine ⟨rfl, by simp, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      omega

/-- **The classical preparation**: moving the witness blocks into the copies and copying the input
into them. -/
theorem classicalRun_prep (hnp : n + p ≤ m) (hm : m ≤ W) (hW : n + 2 * R * p ≤ W)
    (X : Fin (Amplify.width W (2 * R) R) → Bool) (hX : ∀ c, n ≤ c → readBit X c = false)
    (Z : Fin (2 * R * p) → Bool) :
    classicalRun ((moveInCodes n p W (2 * R) ++ moveOutCodes n p W (2 * R)) ++
        Amplify.copyCodes n W (2 * R)) (glue (blockEmb n (witBlock_le hW)) Z X) =
      glue (slotsEmb hnp hm) Z (classicalRun (Amplify.copyCodes n W (2 * R)) X) := by
  rw [classicalRun_append, classicalRun_moveCodes hnp hm hW X hX Z]
  refine classicalRun_glue _ (fun g hg q => ?_) (fun g hg q => ?_) Z X
  · simp only [Amplify.copyCodes, List.mem_flatMap, List.mem_range, List.mem_map] at hg
    obtain ⟨j, hj, i, hi, rfl⟩ := hg
    obtain ⟨⟨j', i'⟩, rfl⟩ := finProdFinEquiv.surjective q
    rw [slotsEmb_finProdFinEquiv, slotEmb_apply_val]
    intro h
    have := eq_of_add_mul_eq (W := W) (a := i' + n) (a' := i) (b := j' + 1) (b' := j + 1)
      (by omega) (by omega) (by simpa only [Nat.add_assoc] using h)
    omega
  · simp only [Amplify.copyCodes, List.mem_flatMap, List.mem_range, List.mem_map] at hg
    obtain ⟨j, hj, i, hi, rfl⟩ := hg
    obtain ⟨⟨j', i'⟩, rfl⟩ := finProdFinEquiv.surjective q
    rw [slotsEmb_finProdFinEquiv, slotEmb_apply_val]
    have := le_add_mul (W := W) (i := (i' : ℕ) + n) (j := j')
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- The state after the classical preparation: the witness on the witness qubits of the copies. -/
theorem eval_prep (hnp : n + p ≤ m) (hm : m ≤ W) (hW : n + 2 * R * p ≤ W) (hW0 : 0 < W)
    (X : Fin (Amplify.width W (2 * R) R) → Bool) (hX : ∀ c, n ≤ c → readBit X c = false)
    (Ψ : Qubits (2 * R * p)) :
    Circuit.eval (Circuit.ofCodes (Amplify.width W (2 * R) R)
        ((moveInCodes n p W (2 * R) ++ moveOutCodes n p W (2 * R)) ++
          Amplify.copyCodes n W (2 * R)))
        (embedState (blockEmb n (witBlock_le hW)) X Ψ) =
      embedState (slotsEmb hnp hm) (classicalRun (Amplify.copyCodes n W (2 * R)) X) Ψ :=
  Circuit.eval_ofCodes_embedState (IsClassical.append.mpr ⟨isClassical_moveCodes hW,
    Amplify.isClassical_copyCodes (by omega) hW0⟩) _ _ _ _ (classicalRun_prep hnp hm hW X hX) Ψ

/-- The bits of a copy after writing the witness blocks: the witness on its witness qubits. -/
theorem glue_slotsEmb_comp_copyEmb (hnp : n + p ≤ m) (hm : m ≤ W) (Z : Fin (2 * R * p) → Bool)
    (X : Fin (Amplify.width W (2 * R) R) → Bool) (j : Fin (2 * R)) :
    glue (slotsEmb hnp hm) Z X ∘ copyEmb hm j =
      glue (blockEmb n hnp) (fun i => Z (finProdFinEquiv (j, i))) (X ∘ copyEmb hm j) := by
  funext i
  by_cases hi : ∃ i', blockEmb n hnp i' = i
  · obtain ⟨i', rfl⟩ := hi
    have : copyEmb hm j (blockEmb n hnp i') = slotsEmb hnp hm (finProdFinEquiv (j, i')) := by
      rw [slotsEmb_finProdFinEquiv]
      rfl
    rw [Function.comp_apply, this, glue_apply_emb, glue_apply_emb]
  · push Not at hi
    rw [Function.comp_apply, glue_of_not _ _ _ fun q h => ?_, glue_of_not _ _ _ hi]
    · rfl
    obtain ⟨⟨j', i'⟩, rfl⟩ := finProdFinEquiv.surjective q
    rw [slotsEmb_finProdFinEquiv] at h
    have h' : (i' : ℕ) + n + (j' + 1) * W = i + (j + 1) * W := congrArg Fin.val h
    have := eq_of_add_mul_eq (lt_of_lt_of_le (show (i' : ℕ) + n < m by omega) hm)
      (lt_of_lt_of_le i.2 hm) h'
    exact hi i' (Fin.ext (by simp; omega))

/-- The copies of the original circuit, on the copies of the original register. -/
theorem ofCodes_copiesCodes_copyEmb (hm : m ≤ W) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, WellFormed m g) :
    Circuit.ofCodes (Amplify.width W (2 * R) R) (Amplify.copiesCodes W (2 * R) gs) =
      ((List.finRange (2 * R)).map (copyEmb hm)).flatMap
        (Circuit.mapWires · (Circuit.ofCodes m gs)) := by
  rw [Amplify.copiesCodes, Circuit.ofCodes_flatMap, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, List.flatMap_map]
  congr 1
  funext j
  exact Circuit.ofCodes_map_shift _ hgs

/-- The copies of the original register are disjoint. -/
theorem pairwise_copyEmb (hm : m ≤ W) :
    ((List.finRange (2 * R)).map (copyEmb hm)).Pairwise fun e e' => ∀ i i', e i ≠ e' i' := by
  rw [List.pairwise_map]
  refine (List.nodup_finRange _).imp fun {j j'} hjj' i i' h => hjj' ?_
  exact congrArg Prod.fst ((copiesEmb hm).injective (a₁ := (j, i)) (a₂ := (j', i')) h)

/-- The amplitudes of one run of the original verifier circuit `gs` on the input `x`: outcome `u` on
the basis witness `w`. -/
noncomputable def amp (hnp : n + p ≤ m) (gs : List GateCode) (x : List Bool) (u : Fin m → Bool)
    (w : Fin p → Bool) : ℂ :=
  (Circuit.run (Circuit.ofCodes m gs) (glue (blockEmb n hnp) w (inputState m x))).ofLp u

/-- **The gate codes of the amplified verifier**: move the `2 R` witness blocks into the witness
qubits of `2 R` copies of the original register (of width at most `W`), copy the input into them,
run the original circuit `gs` on each copy, and take the strict majority of their answers with the
reversible counter of `Cslib.Quantum.Amplify`. -/
def codes (n p W R : ℕ) (gs : List GateCode) : List GateCode :=
  (moveInCodes n p W (2 * R) ++ moveOutCodes n p W (2 * R)) ++ Amplify.codes n W (2 * R) R gs

/-- The gate codes of the amplified verifier, grouped into the classical preparation, the copies of
the original circuit, and the counter. -/
theorem codes_eq (n p W R : ℕ) (gs : List GateCode) :
    codes n p W R gs =
      ((moveInCodes n p W (2 * R) ++ moveOutCodes n p W (2 * R)) ++
          Amplify.copyCodes n W (2 * R)) ++
        (Amplify.copiesCodes W (2 * R) gs ++
          (Counter.codes (Amplify.base W (2 * R)) (R + 1) (fun s => (s + 1) * W) (2 * R) ++
            swapCodes (Amplify.answer W (2 * R) R))) := by
  simp only [codes, Amplify.codes, List.append_assoc]

/-- The input state is zero past the end of the input word. -/
private theorem readBit_inputState_of_length_le {N : ℕ} {x : List Bool} {c : ℕ}
    (hc : x.length ≤ c) : readBit (inputState N x) c = false := by
  by_cases hcN : c < N
  · rw [readBit_of_lt _ hcN]
    change x.getD c false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc]
    rfl
  · exact readBit_of_le _ (not_lt.mp hcN)

/-- **After the copy step, every copy holds the input**: copying the input word `x` (of length
`n ≤ W`) into the copies puts `inputState m x` on each copy of the original register. -/
private theorem classicalRun_copyCodes_comp_copyEmb (hm : m ≤ W) (hn : n ≤ W) (hW0 : 0 < W)
    {x : List Bool} (hx : x.length = n) (j : Fin (2 * R)) :
    classicalRun (Amplify.copyCodes n W (2 * R)) (inputState (Amplify.width W (2 * R) R) x) ∘
      copyEmb hm j = inputState m x := by
  have hlt : (i : Fin m) → (i : ℕ) < Amplify.width W (2 * R) R := fun i =>
    lt_width_of_lt (lt_of_lt_of_le i.2 hm)
  funext i
  have h := Amplify.readBit_classicalRun_copyCodes (k := 2 * R) (t := R) hn hW0 _
    (fun c hc => readBit_inputState_of_length_le (hx.trans_le hc)) (i + (j + 1) * W)
  rw [ite_eq_left ⟨j, j.2, i, lt_of_lt_of_le i.2 hm, rfl⟩, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (lt_of_lt_of_le i.2 hm), readBit_of_lt _ (hlt i)] at h
  rw [Function.comp_apply, ← readBit_fin (classicalRun _ _) (copyEmb hm j i), copyEmb_apply_val, h]
  rfl

/-- After the copy step, the qubits from the counter on are still zero. -/
private theorem readBit_classicalRun_copyCodes_of_base_le (hn : n ≤ W) (hW0 : 0 < W)
    {x : List Bool} (hx : x.length = n) {c : ℕ} (hc : Amplify.base W (2 * R) ≤ c) :
    readBit (classicalRun (Amplify.copyCodes n W (2 * R))
      (inputState (Amplify.width W (2 * R) R) x)) c = false := by
  have hhigh : ∀ c, n ≤ c → readBit (inputState (Amplify.width W (2 * R) R) x) c = false :=
    fun c hc => readBit_inputState_of_length_le (hx.trans_le hc)
  have := Amplify.le_base (w := W) (k := 2 * R)
  rw [Amplify.readBit_classicalRun_copyCodes hn hW0 _ hhigh, ite_eq_right, hhigh c (by omega)]
  rintro ⟨j, hj, i, hi, rfl⟩
  exact absurd hc (not_le.mpr (Amplify.block_lt hj hi))

/-- **The amplitudes after the copies of the original circuit**: started on the witness `Ψ` in
the witness qubits of copies that hold the input, the copies of `gs` reach the outcome `Y` with the
amplitude of the `2 R`-fold tensor power of one run of `gs` on the outcomes of the copies, and with
amplitude zero unless `Y` agrees with the start off the copies. -/
private theorem eval_copiesCodes_apply (hnp : n + p ≤ m) (hm : m ≤ W) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, WellFormed m g) {x : List Bool} {X : Fin (Amplify.width W (2 * R) R) → Bool}
    (hX : ∀ j, X ∘ copyEmb hm j = inputState m x) (Ψ : Qubits (2 * R * p))
    (Y : Fin (Amplify.width W (2 * R) R) → Bool) :
    (Circuit.eval (Circuit.ofCodes (Amplify.width W (2 * R) R) (Amplify.copiesCodes W (2 * R) gs))
      (embedState (slotsEmb hnp hm) X Ψ)).ofLp Y =
      if AgreeOff (copiesEmb hm) Y X then
        tensorPowerApply (amp hnp gs x) (Ψ.ofLp ∘ BitString.blocksEquiv.symm)
          (fun j => Y ∘ copyEmb hm j)
      else 0 := by
  -- off the copies, writing the witness blocks changes nothing
  have hoff (Z : Fin (2 * R * p) → Bool) (c : Fin (Amplify.width W (2 * R) R))
      (hc : ∀ q, copiesEmb hm q ≠ c) : glue (slotsEmb hnp hm) Z X c = X c := by
    refine glue_of_not _ _ _ fun q h => ?_
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective q
    exact hc (j, blockEmb n hnp i) (by rw [← h, slotsEmb_finProdFinEquiv]; rfl)
  have hmem (c : Fin (Amplify.width W (2 * R) R)) :
      (∀ e ∈ (List.finRange (2 * R)).map (copyEmb hm), ∀ i, e i ≠ c) ↔
        ∀ q, copiesEmb hm q ≠ c := by
    simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, copiesEmb_apply, Prod.forall]
  have hcond (Z : Fin (2 * R * p) → Bool) :
      (∀ c, (∀ e ∈ (List.finRange (2 * R)).map (copyEmb hm), ∀ i, e i ≠ c) →
        Y c = glue (slotsEmb hnp hm) Z X c) ↔ AgreeOff (copiesEmb hm) Y X := by
    refine forall_congr' fun c => ?_
    rw [hmem c]
    exact ⟨fun h hc => (h hc).trans (hoff Z c hc), fun h hc => (h hc).trans (hoff Z c hc).symm⟩
  rw [embedState_eq_sum, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Circuit.eval_ket_apply,
    ofCodes_copiesCodes_copyEmb hm hgs, Circuit.matrix_flatMap_mapWires _ _ (pairwise_copyEmb hm),
    hcond]
  by_cases hY : AgreeOff (copiesEmb hm) Y X
  · simp only [hY, ↓reduceIte, tensorPowerApply]
    refine Fintype.sum_equiv BitString.blocksEquiv _ _ fun Z => ?_
    rw [List.map_map, ← Fin.prod_univ_def, Function.comp_apply, Equiv.symm_apply_apply]
    congr 1
    refine prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    rw [glue_slotsEmb_comp_copyEmb, hX, ← Circuit.eval_ket_apply]
    rfl
  · simp [hY]

/-- **The counter takes the majority vote of the copies**: on an outcome `Y` that agrees off the
copies with a register whose qubits from the counter on are zero, the counter and the final swap
accept exactly when more than `R` of the `2 R` copies accept. -/
private theorem classicalRun_counter_swap_mem_accepting_iff (hm : m ≤ W) (hm0 : 0 < m)
    {X Y : Fin (Amplify.width W (2 * R) R) → Bool}
    (hX : ∀ c, Amplify.base W (2 * R) ≤ c → readBit X c = false)
    (hY : AgreeOff (copiesEmb hm) Y X) :
    classicalRun (Counter.codes (Amplify.base W (2 * R)) (R + 1) (fun s => (s + 1) * W) (2 * R) ++
        swapCodes (Amplify.answer W (2 * R) R)) Y ∈ accepting (Amplify.width W (2 * R) R) ↔
      R < (univ.filter fun j : Fin (2 * R) => Y ∘ copyEmb hm j ∈ accepting m).card := by
  have hW0 : 0 < W := by omega
  -- the counter qubits of `Y` lie off the copies, so they are zero
  have hYhigh (c : ℕ) (hc : Amplify.base W (2 * R) ≤ c) : readBit Y c = false := by
    rw [← hX c hc]
    by_cases hcN : c < Amplify.width W (2 * R) R
    · rw [readBit_of_lt _ hcN, readBit_of_lt _ hcN]
      refine hY _ fun q h => ?_
      have h' : (q.2 : ℕ) + (q.1 + 1) * W = c := congrArg Fin.val h
      have := Amplify.block_lt (k := 2 * R) q.1.2 (lt_of_lt_of_le q.2.2 hm)
      omega
    · rw [readBit_of_le _ (not_lt.mp hcN), readBit_of_le _ (not_lt.mp hcN)]
  -- the counter counts the copies whose answer qubit is one
  have hbit (j : Fin (2 * R)) : readBit Y ((j + 1) * W) = (Y ∘ copyEmb hm j) ⟨0, hm0⟩ := by
    rw [Function.comp_apply, ← readBit_fin Y (copyEmb hm j ⟨0, hm0⟩)]
    congr 1
    simp
  have hcount : Counter.count Y (fun s => (s + 1) * W) (2 * R) =
      (univ.filter fun j : Fin (2 * R) => Y ∘ copyEmb hm j ∈ accepting m).card := by
    unfold Counter.count
    rw [← card_map Fin.valEmbedding]
    congr 1
    ext s
    simp only [mem_filter, mem_range, mem_map, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_accepting hm0]
    constructor
    · rintro ⟨hs, h⟩
      exact ⟨⟨s, hs⟩, (hbit ⟨s, hs⟩).symm.trans h, rfl⟩
    · rintro ⟨j, h, rfl⟩
      exact ⟨j.2, (hbit j).trans h⟩
  have h0 : 0 < Amplify.width W (2 * R) R := lt_width_of_lt hW0
  rw [mem_accepting h0, ← readBit_fin (classicalRun _ Y) (⟨0, h0⟩ : Fin _)]
  change readBit _ 0 = true ↔ _
  rw [Amplify.readBit_classicalRun_counter_swap hW0 Y hYhigh, hcount, decide_eq_true_iff]

/-- **The acceptance probability of the amplified verifier** on the witness `Ψ` for the `2 R`
blocks: the weight of the outcomes of the `2 R` copies of the original circuit in which more than
`R` copies accept, under the `2 R`-fold tensor power of the original circuit applied to `Ψ`. -/
theorem measureProb_codes (hnp : n + p ≤ m) (hm : m ≤ W) (hW : n + 2 * R * p ≤ W) (hm0 : 0 < m)
    {gs : List GateCode} (hgs : ∀ g ∈ gs, WellFormed m g) (x : List Bool) (hx : x.length = n)
    (Ψ : Qubits (2 * R * p)) :
    measureProb (Circuit.eval (Circuit.ofCodes (Amplify.width W (2 * R) R) (codes n p W R gs))
        (embedState (blockEmb n (witBlock_le hW)) (inputState (Amplify.width W (2 * R) R) x) Ψ))
        (accepting (Amplify.width W (2 * R) R)) =
      ∑ u : Fin (2 * R) → Fin m → Bool with R < (univ.filter fun j => u j ∈ accepting m).card,
        ‖tensorPowerApply (amp hnp gs x) (Ψ.ofLp ∘ BitString.blocksEquiv.symm) u‖ ^ 2 := by
  have hW0 : 0 < W := by omega
  have hnW : n ≤ W := by omega
  -- the classical preparation puts the witness and the input on the copies
  set X1 := classicalRun (Amplify.copyCodes n W (2 * R)) (inputState (Amplify.width W (2 * R) R) x)
  have hsplit : Circuit.eval (Circuit.ofCodes (Amplify.width W (2 * R) R) (codes n p W R gs))
      (embedState (blockEmb n (witBlock_le hW)) (inputState (Amplify.width W (2 * R) R) x) Ψ) =
      Circuit.eval (Circuit.ofCodes (Amplify.width W (2 * R) R)
        (Counter.codes (Amplify.base W (2 * R)) (R + 1) (fun s => (s + 1) * W) (2 * R) ++
          swapCodes (Amplify.answer W (2 * R) R)))
      (Circuit.eval (Circuit.ofCodes (Amplify.width W (2 * R) R) (Amplify.copiesCodes W (2 * R) gs))
        (embedState (slotsEmb hnp hm) X1 Ψ)) := by
    rw [codes_eq, Circuit.ofCodes_append, Circuit.eval_append,
      eval_prep hnp hm hW hW0 _ fun c hc => readBit_inputState_of_length_le (hx.trans_le hc),
      Circuit.ofCodes_append, Circuit.eval_append]
  -- the acceptance probability as a sum over the outcomes of the copies
  rw [hsplit, Circuit.measureProb_eval_ofCodes (Amplify.isClassical_counter_swap hW0)]
  simp only [eval_copiesCodes_apply hnp hm hgs (X := X1)
    (classicalRun_copyCodes_comp_copyEmb hm hnW hW0 hx) Ψ]
  set T := tensorPowerApply (amp hnp gs x) (Ψ.ofLp ∘ BitString.blocksEquiv.symm)
  set F : (Fin (2 * R) × Fin m → Bool) → ℝ := fun z =>
    if R < (univ.filter fun j => (fun i => z (j, i)) ∈ accepting m).card then
      ‖T (fun j i => z (j, i))‖ ^ 2 else 0 with hF
  have hterm (Y : Fin (Amplify.width W (2 * R) R) → Bool) :
      (if classicalRun (Counter.codes (Amplify.base W (2 * R)) (R + 1) (fun s => (s + 1) * W)
          (2 * R) ++ swapCodes (Amplify.answer W (2 * R) R)) Y ∈
          accepting (Amplify.width W (2 * R) R) then
        ‖if AgreeOff (copiesEmb hm) Y X1 then T (fun j => Y ∘ copyEmb hm j) else 0‖ ^ 2
        else 0) =
      if AgreeOff (copiesEmb hm) Y X1 then F (Y ∘ copiesEmb hm) else 0 := by
    by_cases hY : AgreeOff (copiesEmb hm) Y X1
    · rw [if_congr (classicalRun_counter_swap_mem_accepting_iff hm hm0
        (fun c hc => readBit_classicalRun_copyCodes_of_base_le hnW hW0 hx hc) hY) rfl rfl]
      simp only [hY, ↓reduceIte, hF]
      rfl
    · simp [hY]
  rw [sum_congr rfl fun Y _ => hterm Y, sum_agreeOff_comp (copiesEmb hm) X1 F, sum_filter]
  exact Fintype.sum_equiv (Equiv.curry _ _ _) _ _ fun z => rfl

/-! ### The amplified verifier is constructed in polynomial time -/

section PolyTime

variable {γ : Type} {enc : γ ↪ List Bool}

/-- The gate codes of the amplified verifier are computed in polynomial time. -/
theorem computableInPolyTime_codes {n p W R : γ → ℕ} {gs : γ → List GateCode}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encUnary)
    (hW : ComputableInPolyTime W enc encUnary) (hR : ComputableInPolyTime R enc encUnary)
    (hgs : ComputableInPolyTime gs enc (encList encGateCode)) :
    ComputableInPolyTime (fun c => codes (n c) (p c) (W c) (R c) (gs c)) enc
      (encList encGateCode) := by
  have h₁ : ComputableInPolyTime (fun c => moveInCodes (n c) (p c) (W c) (2 * R c)) enc
      (encList encGateCode) := by
    unfold moveInCodes
    fun_prop
  have h₂ : ComputableInPolyTime (fun c => moveOutCodes (n c) (p c) (W c) (2 * R c)) enc
      (encList encGateCode) := by
    unfold moveOutCodes
    fun_prop
  have h₃ := Amplify.computableInPolyTime_codes hn hW (k := fun c => 2 * R c) (by fun_prop) hR hgs
  unfold codes
  fun_prop

end PolyTime

end QMAAmplify

namespace UniformVerifierFamily

open QMAAmplify

variable (V : UniformVerifierFamily)

/-- **The amplified verifier family** [Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002], Section 14.2:
on inputs of length `n`, the witness consists of `2 r(n)` blocks of `V`'s witness length; each
block is moved into its own copy of `V`'s register, the `2 r(n)` copies of `V`'s circuit run side
by side, and a reversible majority vote of their answers is measured. -/
def amplify (r : ℕ → ℕ) (hr : ComputableInPolyTime r encUnary encUnary) :
    UniformVerifierFamily where
  width n := Amplify.width (V.width n + 2 * r n * V.witnessLength n) (2 * r n) (r n)
  gates n := codes n (V.witnessLength n) (V.width n + 2 * r n * V.witnessLength n) (r n)
    (V.gates n)
  witnessLength n := 2 * r n * V.witnessLength n
  computableInPolyTime_width := by
    have := V.computableInPolyTime_width
    have := V.computableInPolyTime_witnessLength
    simp only [Amplify.width, Amplify.base]
    fun_prop
  computableInPolyTime_gates := by
    have := V.computableInPolyTime_width
    have := V.computableInPolyTime_witnessLength
    exact computableInPolyTime_codes (by fun_prop) V.computableInPolyTime_witnessLength
      (by fun_prop) hr V.computableInPolyTime_gates
  computableInPolyTime_witnessLength := by
    have := V.computableInPolyTime_witnessLength
    fun_prop
  le_width n := by
    have := V.le_width n
    have := witBlock_le (n := n) (p := V.witnessLength n) (R := r n)
      (W := V.width n + 2 * r n * V.witnessLength n) (by omega)
    omega
  width_pos n := lt_width_of_lt (Nat.lt_of_lt_of_le (V.width_pos n) (Nat.le_add_right _ _))
  add_witnessLength_le n := by
    have := V.le_width n
    exact witBlock_le (n := n) (p := V.witnessLength n) (R := r n)
      (W := V.width n + 2 * r n * V.witnessLength n) (by omega)
  wellFormed n g hg := by
    have hw := V.width_pos n
    have hle := V.le_width n
    have hwit := V.add_witnessLength_le n
    rw [codes_eq] at hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact (isClassical_moveCodes (by omega) g hg).2
      · exact (Amplify.isClassical_copyCodes (by omega) (by omega) g hg).2
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨j, hj, hg⟩ := List.mem_flatMap.mp hg
      obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hg
      have := Amplify.block_le_width (w := V.width n + 2 * r n * V.witnessLength n)
        (k := 2 * r n) (t := r n) (List.mem_range.mp hj)
      exact (V.wellFormed n g hg').shift (by omega)
    · exact (Amplify.isClassical_counter_swap (by omega) g hg).2

/-- The amplitudes of one run of `V` on the input `x`: outcome `u` on the basis witness `w`. -/
noncomputable def amp (x : List Bool) : (Fin (V.width x.length) → Bool) →
    (Fin (V.witnessLength x.length) → Bool) → ℂ :=
  QMAAmplify.amp (V.add_witnessLength_le x.length) (V.gates x.length) x

/-- **The acceptance probability of the amplified family** on the witness `Ψ`: the weight of the
outcomes of `2 r(n)` copies of `V` in which more than `r(n)` copies accept, under the
`2 r(n)`-fold tensor power of `V`'s circuit applied to `Ψ`. -/
theorem acceptProb_amplify {r : ℕ → ℕ} (hr : ComputableInPolyTime r encUnary encUnary)
    (x : List Bool) (Ψ : Qubits ((V.amplify r hr).witnessLength x.length)) :
    (V.amplify r hr).acceptProb x Ψ =
      ∑ u : Fin (2 * r x.length) → Fin (V.width x.length) → Bool with
        r x.length < (univ.filter fun j => u j ∈ accepting (V.width x.length)).card,
        ‖tensorPowerApply (V.amp x)
          (Ψ.ofLp ∘ BitString.blocksEquiv.symm) u‖ ^ 2 := by
  have := V.le_width x.length
  exact measureProb_codes (V.add_witnessLength_le x.length) (Nat.le_add_right _ _) (by omega)
    (V.width_pos x.length) (V.wellFormed x.length) x rfl Ψ

/-- The outcomes of one run of `V` on the witness `φ`. -/
theorem sum_amp_mul (x : List Bool) (φ : (Fin (V.witnessLength x.length) → Bool) → ℂ)
    (u : Fin (V.width x.length) → Bool) :
    ∑ w, V.amp x u w * φ w =
      (Circuit.eval (Circuit.ofCodes (V.width x.length) (V.gates x.length))
        (embedState (V.witnessQubits x.length) (inputState (V.width x.length) x)
          (WithLp.toLp 2 φ : Qubits _))).ofLp u := by
  rw [embedState_eq_sum, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  refine sum_congr rfl fun w _ => ?_
  rw [map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp, mul_comm]
  rfl

/-- One run of `V` is an isometry from the witness to the outcomes. -/
theorem amp_isometry (x : List Bool) (φ : (Fin (V.witnessLength x.length) → Bool) → ℂ) :
    ∑ u, ‖∑ w, V.amp x u w * φ w‖ ^ 2 = ∑ w, ‖φ w‖ ^ 2 := by
  simp only [V.sum_amp_mul x φ]
  rw [← EuclideanSpace.norm_sq_eq, LinearIsometryEquiv.norm_map, LinearIsometry.norm_map,
    EuclideanSpace.norm_sq_eq]

/-- The acceptance probability of one run of `V` on the witness `φ`. -/
theorem sum_accepting_amp (x : List Bool) (φ : (Fin (V.witnessLength x.length) → Bool) → ℂ) :
    ∑ u ∈ accepting (V.width x.length), ‖∑ w, V.amp x u w * φ w‖ ^ 2 =
      V.acceptProb x (WithLp.toLp 2 φ) := by
  simp only [V.sum_amp_mul x φ]
  rfl

/-- A bound on the acceptance probability of unit witnesses holds for all witnesses, scaled by the
squared norm. -/
theorem acceptProb_le_mul_norm_sq {x : List Bool} {s : ℝ}
    (h : ∀ ψ : Qubits (V.witnessLength x.length), ‖ψ‖ = 1 → V.acceptProb x ψ ≤ s)
    (ψ : Qubits (V.witnessLength x.length)) : V.acceptProb x ψ ≤ s * ‖ψ‖ ^ 2 := by
  by_cases hψ : ψ = 0
  · have := V.acceptProb_le x ψ
    rw [hψ, norm_zero] at this ⊢
    nlinarith [V.acceptProb_nonneg x 0]
  · have hn : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    have h1 := h _ (norm_smul_inv_norm (𝕜 := ℂ) hψ)
    rw [acceptProb_smul, norm_inv, RCLike.norm_ofReal, abs_norm] at h1
    have hpos : 0 < ‖ψ‖ ^ 2 := by positivity
    have : (‖ψ‖⁻¹) ^ 2 * V.acceptProb x ψ * ‖ψ‖ ^ 2 = V.acceptProb x ψ := by
      field_simp
    nlinarith

/-- **Amplifying soundness** [Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002], Section 14.2: if `V`
accepts every unit witness with probability at most `1 / 3`, then the amplified family accepts
every witness, entangled across the blocks or not, with probability at most `(8 / 9) ^ r(n)` times
its squared norm. -/
theorem acceptProb_amplify_le {r : ℕ → ℕ} (hr : ComputableInPolyTime r encUnary encUnary)
    {x : List Bool}
    (hx : ∀ ψ : Qubits (V.witnessLength x.length), ‖ψ‖ = 1 → V.acceptProb x ψ ≤ 1 / 3)
    (Ψ : Qubits ((V.amplify r hr).witnessLength x.length)) :
    (V.amplify r hr).acceptProb x Ψ ≤ (8 / 9) ^ r x.length * ‖Ψ‖ ^ 2 := by
  set R := r x.length
  have hm0 := V.width_pos x.length
  have hA' (φ : (Fin (V.witnessLength x.length) → Bool) → ℂ) :
      ∑ u ∈ accepting (V.width x.length), ‖∑ w, V.amp x u w * φ w‖ ^ 2 ≤
        1 / 3 * ∑ w, ‖φ w‖ ^ 2 := by
    rw [V.sum_accepting_amp x φ]
    refine (V.acceptProb_le_mul_norm_sq hx _).trans_eq ?_
    rw [EuclideanSpace.norm_sq_eq]
  have hbound := sum_card_filter_ge_norm_tensorPowerApply_le (V.amp x)
    (accepting (V.width x.length)) (1 / 3) hA' (V.amp_isometry x) (by norm_num) le_rfl
    (r := R) (Ψ.ofLp ∘ BitString.blocksEquiv.symm)
  rw [sum_norm_tensorPowerApply _ (V.amp_isometry x)] at hbound
  have hΨ : ∑ w, ‖(Ψ.ofLp ∘ BitString.blocksEquiv.symm) w‖ ^ 2 =
      ‖Ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Fintype.sum_equiv BitString.blocksEquiv.symm _ _
      fun w => rfl
  rw [hΨ] at hbound
  rw [acceptProb_amplify]
  refine le_trans (sum_le_sum_of_subset_of_nonneg (fun u hu => ?_)
    fun u _ _ => by positivity) hbound
  rw [mem_filter] at hu ⊢
  exact ⟨mem_univ _, hu.2.le⟩

/-- **Amplifying completeness** [Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002], Section 14.2: if `V`
accepts the unit witness `ψ` with probability at least `2 / 3`, then the amplified family accepts
the unit witness `ψ^{⊗ 2 r(n)}` with probability at least `1 - (8 / 9) ^ r(n)`. -/
theorem exists_one_sub_le_acceptProb_amplify {r : ℕ → ℕ}
    (hr : ComputableInPolyTime r encUnary encUnary) {x : List Bool}
    {ψ : Qubits (V.witnessLength x.length)} (hψ : ‖ψ‖ = 1)
    (hx : 2 / 3 ≤ V.acceptProb x ψ) :
    ∃ Ψ : Qubits ((V.amplify r hr).witnessLength x.length), ‖Ψ‖ = 1 ∧
      1 - (8 / 9) ^ r x.length ≤ (V.amplify r hr).acceptProb x Ψ := by
  let Ψ : Qubits ((V.amplify r hr).witnessLength x.length) := WithLp.toLp 2 fun Z =>
    ∏ j, ψ.ofLp (BitString.blocksEquiv Z j)
  have hψsum : ∑ w, ‖ψ.ofLp w‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]
  have hΨsq : ‖Ψ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ Z, ‖Ψ.ofLp Z‖ ^ 2
        = ∑ u : Fin (2 * r x.length) → Fin (V.witnessLength x.length) → Bool,
            ∏ j, ‖ψ.ofLp (u j)‖ ^ 2 :=
          Fintype.sum_equiv BitString.blocksEquiv _ _
            fun Z => by rw [prod_pow, ← norm_prod]
      _ = 1 := by rw [← Fintype.sum_pow (fun w => ‖ψ.ofLp w‖ ^ 2), hψsum, one_pow]
  refine ⟨Ψ, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hΨsq, ?_⟩
  rw [acceptProb_amplify]
  -- on the product witness, the copies are independent
  have hprod (u : Fin (2 * r x.length) → Fin (V.width x.length) → Bool) :
      tensorPowerApply (V.amp x)
        (Ψ.ofLp ∘ BitString.blocksEquiv.symm) u =
        ∏ j, ∑ w, V.amp x (u j) w * ψ.ofLp w := by
    rw [tensorPowerApply, Fintype.prod_sum]
    refine sum_congr rfl fun w _ => ?_
    change (∏ j, ψ.ofLp (BitString.blocksEquiv (BitString.blocksEquiv.symm w) j)) * _ = _
    rw [Equiv.apply_symm_apply, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => mul_comm _ _
  simp only [hprod, norm_prod, ← prod_pow]
  have hq0 (v : Fin (V.width x.length) → Bool) : 0 ≤ ‖∑ w, V.amp x v w * ψ.ofLp w‖ ^ 2 := by
    positivity
  have hqsum := V.amp_isometry x ψ.ofLp
  rw [hψsum] at hqsum
  have hqacc := V.sum_accepting_amp x ψ.ofLp
  rw [WithLp.toLp_ofLp] at hqacc
  have hbad := sum_prod_le_of_card_filter_le (fun v => ‖∑ w, V.amp x v w * ψ.ofLp w‖ ^ 2) hq0
    hqsum (accepting (V.width x.length)) (by rw [hqacc]; linarith) (r x.length)
  have htotal := (Fintype.sum_pow (fun v => ‖∑ w, V.amp x v w * ψ.ofLp w‖ ^ 2)
    (2 * r x.length)).symm
  rw [hqsum, one_pow, ← sum_filter_add_sum_filter_not univ
    (fun u : Fin (2 * r x.length) → Fin (V.width x.length) → Bool =>
      r x.length < (univ.filter fun j => u j ∈ accepting (V.width x.length)).card)] at htotal
  simp only [not_lt] at htotal
  linarith

end UniformVerifierFamily

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Weak error reduction for `QMA`** [Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002], Section 14.2;
[Marriott, Watrous][MarriottWatrous2005], Theorem 3.2 at the gap `(2 / 3, 1 / 3)`: for every
polynomial `q`, `QMA(2 / 3, 1 / 3) ⊆ QMA(1 - 2^{-q}, 2^{-q})`. The amplified verifier takes
`12 q(n)` copies of the witness length. -/
theorem PromiseQMA_subset_errorExponent (q : Polynomial ℕ) :
    PromiseQMA (fun _ => 2 / 3) (fun _ => 1 / 3) enc ⊆
      PromiseQMA (fun n => 1 - ((2 : ℝ) ^ q.eval n)⁻¹) (fun n => ((2 : ℝ) ^ q.eval n)⁻¹) enc := by
  rintro Q ⟨V, hV⟩
  have hr : ComputableInPolyTime (fun n => 6 * q.eval n) encUnary encUnary := by fun_prop
  refine ⟨V.amplify _ hr, fun a => ⟨fun ha => ?_, fun ha Ψ hΨ => ?_⟩⟩
  · obtain ⟨ψ, hψ, h⟩ := (hV a).1 ha
    obtain ⟨Ψ, hΨ, h'⟩ := V.exists_one_sub_le_acceptProb_amplify hr hψ h
    refine ⟨Ψ, hΨ, le_trans ?_ h'⟩
    have := eight_ninths_pow_le (q.eval (enc a).length)
    dsimp only
    linarith
  · have h := V.acceptProb_amplify_le hr ((hV a).2 ha) Ψ
    rw [hΨ, one_pow, mul_one] at h
    exact h.trans (eight_ninths_pow_le _)

/-- Conversely, `QMA(1 - 2^{-q}, 2^{-q}) ⊆ QMA(2 / 3, 1 / 3)` when `q ≥ 2`. -/
theorem PromiseQMA_errorExponent_subset (q : Polynomial ℕ) (hq : ∀ n, 2 ≤ q.eval n) :
    PromiseQMA (fun n => 1 - ((2 : ℝ) ^ q.eval n)⁻¹) (fun n => ((2 : ℝ) ^ q.eval n)⁻¹) enc ⊆
      PromiseQMA (fun _ => 2 / 3) (fun _ => 1 / 3) enc := by
  have h (n : ℕ) : ((2 : ℝ) ^ q.eval n)⁻¹ ≤ 1 / 3 := by
    have : (4 : ℝ) ≤ 2 ^ q.eval n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.eval n := pow_le_pow_right₀ (by norm_num) (hq n)
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  exact PromiseQMA_mono (fun n => by linarith [h n]) h

/-- **Error reduction for `QMA`**: a problem is in `QMA` exactly when, for every polynomial `q`, it
has a polynomial-time uniform family of verifiers with completeness `1 - 2^{-q(n)}` and soundness
`2^{-q(n)}`, where `n` is the length of the encoded instance. -/
theorem mem_QMA_iff_forall_errorExponent {A : Set α} :
    A ∈ QMA enc ↔ ∀ q : Polynomial ℕ, PromiseProblem.ofSet A ∈
      PromiseQMA (fun n => 1 - ((2 : ℝ) ^ q.eval n)⁻¹) (fun n => ((2 : ℝ) ^ q.eval n)⁻¹) enc :=
  ⟨fun h q => PromiseQMA_subset_errorExponent q h, fun h =>
    PromiseQMA_errorExponent_subset (Polynomial.C 2) (fun n => by simp) (h (Polynomial.C 2))⟩

end Cslib.Complexity
