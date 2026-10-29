/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ReadOnce
public import Complexity.Computability.Complexity.FineGrained.PermutationIndependentSet
public import Complexity.Computability.MCSP.PartialNP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Foundations.Data.BitString.Binary

/-!
# ETH Hardness of Partial-Function MCSP (`PartialMCSP`)

This module formalizes Rahul Ilango's ETH lower bound for partial-function Minimum Circuit Size
Problem (`MCSP*` / `PartialMCSP`) [Ilango2020FOCS, Theorem I.3, pp. 424, 427–428; ECCC TR20-183,
Section 1.2.2, Theorem 3, p. 6, and Section 3, Theorem 11 (p. 20) & Lemma 12 (p. 22),
construction and proof pp. 21–26]: under the Exponential Time Hypothesis (`ETH`), `PartialMCSP` on
partial Boolean functions of arity $m$ (truth-table size $N = 2^m$) is not decidable in
subexponential time $2^{o(m \log m)} = N^{o(\log \log N)}$ (`¬DecidableInSubexpTime`).

## Overview of the reduction and faithfulness

1. **Source problem** (`BipartitePermutationIndependentSet`):
   Given an instance $G = (n, E)$ of `$2n \times 2n$ Bipartite Permutation Independent Set` with
   parameter $n$ and directed pair-edges $E \subseteq ([n] \times [n])^2$, decide whether there
   exist permutations $\sigma_1, \sigma_2 \in S_n$ (equivalently, a block-preserving permutation
   $\pi \in S_{2n}$ on $[0, n) \cup [n, 2n)$) avoiding all conflict edges in $E$. By the
   Lokshtanov–Marx–Saurabh theorem
   (`ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet`,
   [LokshtanovMarxSaurabh2018, Theorem 2.11]; [Ilango2020FOCS, Section III.B, p. 427; ECCC
   TR20-183, Section 3, Theorem 10, p. 20]), this problem cannot be decided in time
   $2^{o(n \log n)}$ under `ETH`.

2. **Ilango's partial Boolean function $\gamma_G$** (`PartialMCSP.ilangoGamma`,
   [Ilango2020FOCS, Section III.B, p. 428; ECCC TR20-183, Section 3, p. 21]):
   For $n = G.1$, $\gamma_G : \{0, 1\}^{6n} \to \mathrm{Option\ Bool}$ views a $6n$-bit input as a
   triple $(x, y, z) \in \{0, 1\}^{2n} \times \{0, 1\}^{2n} \times \{0, 1\}^{2n}$ and is defined by
   seven clauses:
   * (1) If $x = 0^{2n}$: $\bigvee_{i \in [2n]} (y_i \wedge z_i)$.
   * (2) If $x = 1^{2n}$: $\bigvee_{i \in [2n]} z_i$.
   * (3) If $z = 1^{2n}$: $\bigvee_{i \in [2n]} (x_i \vee y_i)$.
   * (4) If $z = 0^{2n}$: $0$ (`false`).
   * (5) If $z = 1^n 0^n$ and $y = 0^{2n}$: $\bigvee_{i < n} x_i$.
   * (6) If $z = 0^n 1^n$ and $y = 0^{2n}$: $\bigvee_{n \le i < 2n} x_i$.
   * (7) If $\exists ((j, k), (j', k')) \in E$ with $(x, y, z) = (\overline{e_k}\,\overline{e_{k'}},
     0^{2n}, e_j\,e_{j'})$: $1$ (`true`).
   * Otherwise: $?$ (`none`).

3. **Rigidity of read-once formulas for Clauses 1–4**
   (`PosFormula.exists_perm_of_agreesWith_ilango`,
   [ECCC TR20-183, Section 3, Lemma 12, pp. 22, 24–26]):
   Any read-once positive formula $F$ on $6n$ variables ($n \ge 1$) of leaf size $6n$ (i.e., binary
   gate size $6n - 1$) that agrees with Clauses (1)–(4) computes
   $(x, y, z) \mapsto \bigvee_{i \in [2n]} ((x_{\pi(i)} \vee y_i) \wedge z_i)$ for some permutation
   $\pi \in S_{2n}$.

4. **Equivalence across circuit and formula models**
   ([ECCC TR20-183, Section 3, Theorem 11, p. 20, construction and proof pp. 21–24]):
   For $n \ge 2$, the instance `ilangoInstance G` of arity $6n$ and threshold $s = 6n - 1$ has all
   $6n$ variables positively essential (`ilangoInstance_posEssential`). By
   `Circuit.exists_posFormula_of_cost_binaryCost_le`, any circuit $c$ with at most $6n - 1$ binary
   (`AND`/`OR`) gates agreeing with $\gamma_G$ unfolds into a read-once positive formula of size
   $6n - 1$. Conversely, any satisfying permutation $\pi \in S_{2n}$ yields an explicit read-once
   positive formula $\bigvee_{i \in [2n]} ((x_{\pi(i)} \vee y_i) \wedge z_i)$ of gate size $6n - 1$
   whose compiled circuit has all-gates size $6n - 1$. Thus for $n \ge 2$:
   $$G \in \mathrm{BipartitePermutationIndependentSet}
     \iff \mathrm{ilangoInstance}\, G \in \mathrm{PartialMCSP}
     \iff \mathrm{ilangoInstance}\, G \in \mathrm{PartialMCSP.BinaryGate}
     \iff \mathrm{ilangoInstance}\, G \in \mathrm{PartialMCSP.MonotoneReadOnce}.$$

## Main definitions

* `Cslib.PartialMCSP.MonotoneReadOnce`: partial-function MCSP restricted to read-once positive
  formulas.
* `Cslib.PartialMCSP.ilangoGamma`, `Cslib.PartialMCSP.ilangoInstance`: Ilango's partial Boolean
  function $\gamma_G$ on $6n$ bits and the `PartialMCSP` instance $(\gamma_G, 6n - 1)$.
* `Cslib.PartialMCSP.ilangoReduction`: total reduction from `BipartitePermutationGraph` to
  `PartialMCSP` running in time $2^{O(n)} \cdot \mathrm{poly}(|G|)$.

## Main results

* `Cslib.Circuits.Boolean.PosFormula.exists_perm_of_agreesWith_ilango`: Ilango's Lemma 12
  [ECCC TR20-183, Section 3, Lemma 12, pp. 22, 24–26].
* `Cslib.PartialMCSP.mem_BipartitePermutationIndependentSet_iff_ilangoInstance_mem`: correctness of
  `ilangoInstance` for $2 \le G.1$ across `PartialMCSP`, `PartialMCSP.BinaryGate`, and
  `PartialMCSP.MonotoneReadOnce` [ECCC TR20-183, Section 3, Theorem 11, p. 20, proof pp. 21–24].
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_encBinary`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate_encBinary`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_monotoneReadOnce`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_monotoneReadOnce_encBinary`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_tableSize`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_tableSize_encBinary`: Ilango's FOCS
  2020 Theorem I.3 / ECCC TR20-183 Section 1.2.2 Theorem 3 (under `ETH`, `PartialMCSP` and its
  binary-gate and monotone-read-once variants reject the subexponential decider family
  `DecidableInSubexpTime` at $m \log_2 m = \log_2 N \cdot \log_2 \log_2 N$, i.e., are not decidable
  in time $2^{o(m \log m)} = N^{o(\log \log N)}$).

## References

* [R. Ilango, *Constant Depth Formula and Partial Function Versions of MCSP are
  Hard*][Ilango2020FOCS]
* [D. Lokshtanov, D. Marx, S. Saurabh, *Slightly Superexponential Parameterized
  Problems*][LokshtanovMarxSaurabh2018]
-/

public section

namespace Cslib

open Circuits Circuits.Boolean Complexity Turing.MultiTapeTM

namespace PartialMCSP

/-! ### Read-once monotone formula variant of `PartialMCSP` -/

/-- **Read-once positive formula variant of `PartialMCSP`** [Ilango2020FOCS, Section III.B; ECCC
TR20-183, Section 3, Theorem 11, p. 20]: instances `x : PartialMCSP.Instance` that agree with some
read-once positive Boolean formula `F : PosFormula x.arity` with at most `x.threshold` binary
gates. -/
@[expose] def MonotoneReadOnce : Set Instance :=
  {x | ∃ F : PosFormula x.arity, F.IsReadOnce ∧ F.size ≤ x.threshold ∧ x.AgreesWith F.eval}

theorem mem_monotoneReadOnce_iff {x : Instance} :
    x ∈ MonotoneReadOnce ↔
      ∃ F : PosFormula x.arity, F.IsReadOnce ∧ F.size ≤ x.threshold ∧ x.AgreesWith F.eval :=
  Iff.rfl

/-- Every yes-instance of `PartialMCSP.MonotoneReadOnce` is a yes-instance of all-gates
`PartialMCSP`, since `F.toCircuit` has `F.toCircuit.size = F.size`. -/
theorem mem_of_mem_monotoneReadOnce {x : Instance} (h : x ∈ MonotoneReadOnce) :
    x ∈ PartialMCSP := by
  obtain ⟨F, -, hsize, hagree⟩ := h
  rw [mem_iff_exists_circuit]
  refine ⟨F.toCircuit, by simpa using hsize, fun y b hy => ?_⟩
  rw [PosFormula.eval_toCircuit]
  exact hagree y b hy

theorem monotoneReadOnce_subset : MonotoneReadOnce ⊆ PartialMCSP :=
  fun _ => mem_of_mem_monotoneReadOnce

theorem monotoneReadOnce_subset_binaryGate : MonotoneReadOnce ⊆ BinaryGate :=
  fun _ h => mem_binaryGate_of_mem (mem_of_mem_monotoneReadOnce h)

/-! ### Block-of-three-$2n$ coordinates `(x, y, z)` on `Fin (6 * n)` -/

variable {n : ℕ}

/-- Coordinate `i : Fin (2 * n)` of the first block `x` in `Fin (6 * n)`. -/
@[expose] def xVar (i : Fin (2 * n)) : Fin (6 * n) :=
  ⟨i.1, by omega⟩

/-- Coordinate `i : Fin (2 * n)` of the second block `y` in `Fin (6 * n)`. -/
@[expose] def yVar (i : Fin (2 * n)) : Fin (6 * n) :=
  ⟨2 * n + i.1, by omega⟩

/-- Coordinate `i : Fin (2 * n)` of the third block `z` in `Fin (6 * n)`. -/
@[expose] def zVar (i : Fin (2 * n)) : Fin (6 * n) :=
  ⟨4 * n + i.1, by omega⟩

private theorem xVar_injective : Function.Injective (xVar (n := n)) := by
  intro i j h
  ext
  exact Fin.mk.inj h

private theorem yVar_injective : Function.Injective (yVar (n := n)) := by
  intro i j h
  ext
  have := Fin.mk.inj h
  omega

private theorem zVar_injective : Function.Injective (zVar (n := n)) := by
  intro i j h
  ext
  have := Fin.mk.inj h
  omega

@[simp] private theorem xVar_inj {i j : Fin (2 * n)} : xVar i = xVar j ↔ i = j :=
  xVar_injective.eq_iff

@[simp] private theorem yVar_inj {i j : Fin (2 * n)} : yVar i = yVar j ↔ i = j :=
  yVar_injective.eq_iff

@[simp] private theorem zVar_inj {i j : Fin (2 * n)} : zVar i = zVar j ↔ i = j :=
  zVar_injective.eq_iff

private theorem xVar_ne_yVar (i j : Fin (2 * n)) : xVar i ≠ yVar j := by
  intro h
  have := Fin.mk.inj h
  omega

private theorem xVar_ne_zVar (i j : Fin (2 * n)) : xVar i ≠ zVar j := by
  intro h
  have := Fin.mk.inj h
  omega

private theorem yVar_ne_zVar (i j : Fin (2 * n)) : yVar i ≠ zVar j := by
  intro h
  have := Fin.mk.inj h
  omega

/-- Every coordinate in `Fin (6 * n)` belongs to the `x`, `y`, or `z` block. -/
private theorem eq_xVar_or_yVar_or_zVar (v : Fin (6 * n)) :
    (∃ i, v = xVar i) ∨ (∃ i, v = yVar i) ∨ (∃ i, v = zVar i) := by
  by_cases h₁ : v.1 < 2 * n
  · exact Or.inl ⟨⟨v.1, h₁⟩, rfl⟩
  · by_cases h₂ : v.1 < 4 * n
    · refine Or.inr (Or.inl ⟨⟨v.1 - 2 * n, by omega⟩, ?_⟩)
      ext; dsimp [yVar]; omega
    · refine Or.inr (Or.inr ⟨⟨v.1 - 4 * n, by omega⟩, ?_⟩)
      ext; dsimp [zVar]; omega

/-- The finset of `z`-coordinates in `Fin (6 * n)`. -/
private def zSet (n : ℕ) : Finset (Fin (6 * n)) :=
  Finset.univ.image zVar

private theorem mem_zSet {v : Fin (6 * n)} : v ∈ zSet n ↔ ∃ i, v = zVar i := by
  simp [zSet, eq_comm]

@[simp] private theorem zVar_mem_zSet (i : Fin (2 * n)) : zVar i ∈ zSet n :=
  mem_zSet.mpr ⟨i, rfl⟩

@[simp] private theorem xVar_notMem_zSet (i : Fin (2 * n)) : xVar i ∉ zSet n := by
  rw [mem_zSet]
  rintro ⟨j, hj⟩
  exact xVar_ne_zVar i j hj

@[simp] private theorem yVar_notMem_zSet (i : Fin (2 * n)) : yVar i ∉ zSet n := by
  rw [mem_zSet]
  rintro ⟨j, hj⟩
  exact yVar_ne_zVar i j hj

@[simp] private theorem card_zSet (n : ℕ) : (zSet n).card = 2 * n := by
  rw [zSet, Finset.card_image_of_injective _ zVar_injective, Finset.card_univ, Fintype.card_fin]

/-- Extract the `x`-block of a $6n$-bit string. -/
@[expose] def unpackX (w : BitString (6 * n)) : BitString (2 * n) :=
  fun i => w (xVar i)

/-- Extract the `y`-block of a $6n$-bit string. -/
@[expose] def unpackY (w : BitString (6 * n)) : BitString (2 * n) :=
  fun i => w (yVar i)

/-- Extract the `z`-block of a $6n$-bit string. -/
@[expose] def unpackZ (w : BitString (6 * n)) : BitString (2 * n) :=
  fun i => w (zVar i)

/-- Pack three $2n$-bit strings `(x, y, z)` into a single $6n$-bit string. -/
@[expose] def packXYZ (x y z : BitString (2 * n)) (v : Fin (6 * n)) : Bool :=
  if h₁ : v.1 < 2 * n then x ⟨v.1, h₁⟩
  else if h₂ : v.1 < 4 * n then y ⟨v.1 - 2 * n, by omega⟩
  else z ⟨v.1 - 4 * n, by omega⟩

@[simp] private theorem packXYZ_xVar (x y z : BitString (2 * n)) (i : Fin (2 * n)) :
    packXYZ x y z (xVar i) = x i := by
  simp [packXYZ, xVar, i.2]

@[simp] private theorem packXYZ_yVar (x y z : BitString (2 * n)) (i : Fin (2 * n)) :
    packXYZ x y z (yVar i) = y i := by
  have h₁ : ¬(2 * n + i.1 < 2 * n) := by omega
  have h₂ : 2 * n + i.1 < 4 * n := by omega
  simp [packXYZ, yVar, h₁, h₂]

@[simp] private theorem packXYZ_zVar (x y z : BitString (2 * n)) (i : Fin (2 * n)) :
    packXYZ x y z (zVar i) = z i := by
  have h₁ : ¬(4 * n + i.1 < 2 * n) := by omega
  have h₂ : ¬(4 * n + i.1 < 4 * n) := by omega
  simp [packXYZ, zVar, h₁, h₂]

@[simp] private theorem unpackX_packXYZ (x y z : BitString (2 * n)) :
    unpackX (packXYZ x y z) = x := by
  funext i; simp [unpackX]

@[simp] private theorem unpackY_packXYZ (x y z : BitString (2 * n)) :
    unpackY (packXYZ x y z) = y := by
  funext i; simp [unpackY]

@[simp] private theorem unpackZ_packXYZ (x y z : BitString (2 * n)) :
    unpackZ (packXYZ x y z) = z := by
  funext i; simp [unpackZ]

@[simp] private theorem packXYZ_unpack (w : BitString (6 * n)) :
    packXYZ (unpackX w) (unpackY w) (unpackZ w) = w := by
  funext v
  rcases eq_xVar_or_yVar_or_zVar v with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [unpackX, unpackY, unpackZ]

private theorem update_packXYZ_xVar (x y z : BitString (2 * n)) (i : Fin (2 * n)) (b : Bool) :
    Function.update (packXYZ x y z) (xVar i) b = packXYZ (Function.update x i b) y z := by
  funext v
  rcases eq_xVar_or_yVar_or_zVar v with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne (xVar_inj.not.mpr h), Function.update_of_ne h]
  · simp [Function.update_of_ne (xVar_ne_yVar i j).symm]
  · simp [Function.update_of_ne (xVar_ne_zVar i j).symm]

private theorem update_packXYZ_yVar (x y z : BitString (2 * n)) (i : Fin (2 * n)) (b : Bool) :
    Function.update (packXYZ x y z) (yVar i) b = packXYZ x (Function.update y i b) z := by
  funext v
  rcases eq_xVar_or_yVar_or_zVar v with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [Function.update_of_ne (xVar_ne_yVar j i)]
  · by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne (yVar_inj.not.mpr h), Function.update_of_ne h]
  · simp [Function.update_of_ne (yVar_ne_zVar i j).symm]

private theorem update_packXYZ_zVar (x y z : BitString (2 * n)) (i : Fin (2 * n)) (b : Bool) :
    Function.update (packXYZ x y z) (zVar i) b = packXYZ x y (Function.update z i b) := by
  funext v
  rcases eq_xVar_or_yVar_or_zVar v with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [Function.update_of_ne (xVar_ne_zVar j i)]
  · simp [Function.update_of_ne (yVar_ne_zVar j i)]
  · by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne (zVar_inj.not.mpr h), Function.update_of_ne h]

/-! ### Special $2n$-bit vectors and Ilango's partial function $\gamma_G$ -/

/-- All-zeros vector $0^{2n}$. -/
@[expose] def zeros2n : BitString (2 * n) := fun _ => false

/-- All-ones vector $1^{2n}$. -/
@[expose] def ones2n : BitString (2 * n) := fun _ => true

/-- Left-half indicator $1^n 0^n$. -/
@[expose] def leftHalfOnes : BitString (2 * n) := fun i => decide (i.1 < n)

/-- Right-half indicator $0^n 1^n$. -/
@[expose] def rightHalfOnes : BitString (2 * n) := fun i => decide (n ≤ i.1)

/-- Pair-of-units vector $e_j e_{j'} \in \{0, 1\}^{2n}$ with ones at $j$ and $n + j'$. -/
@[expose] def unitPair (j j' : Fin n) : BitString (2 * n) :=
  fun i => decide (i.1 = j.1 ∨ i.1 = n + j'.1)

/-- Complemented pair-of-units vector $\overline{e_k}\,\overline{e_{k'}} \in \{0, 1\}^{2n}$ with
zeros at $k$ and $n + k'$ and ones elsewhere. -/
@[expose] def antiUnitPair (k k' : Fin n) : BitString (2 * n) :=
  fun i => !decide (i.1 = k.1 ∨ i.1 = n + k'.1)

@[simp] private theorem zeros2n_apply (i : Fin (2 * n)) : zeros2n i = false := rfl
@[simp] private theorem ones2n_apply (i : Fin (2 * n)) : ones2n i = true := rfl
@[simp] private theorem leftHalfOnes_apply (i : Fin (2 * n)) : leftHalfOnes i = decide (i.1 < n) :=
  rfl
@[simp] private theorem rightHalfOnes_apply (i : Fin (2 * n)) :
    rightHalfOnes i = decide (n ≤ i.1) := rfl

/-- **Ilango's partial Boolean function $\gamma_G$** [Ilango2020FOCS, Section III.B, p. 428; ECCC
TR20-183, Section 3, p. 21] on $6n$ variables for a `BipartitePermutationGraph` $G = (n, E)$. -/
@[expose] def ilangoGamma (G : BipartitePermutationGraph) (w : BitString (6 * G.1)) : Option Bool :=
  let n := G.1
  let x := unpackX w
  let y := unpackY w
  let z := unpackZ w
  if x = zeros2n then
    some (decide (∃ i : Fin (2 * n), y i = true ∧ z i = true))
  else if x = ones2n then
    some (decide (∃ i : Fin (2 * n), z i = true))
  else if z = ones2n then
    some (decide (∃ i : Fin (2 * n), x i = true ∨ y i = true))
  else if z = zeros2n then
    some false
  else if z = leftHalfOnes ∧ y = zeros2n then
    some (decide (∃ i : Fin (2 * n), i.1 < n ∧ x i = true))
  else if z = rightHalfOnes ∧ y = zeros2n then
    some (decide (∃ i : Fin (2 * n), n ≤ i.1 ∧ x i = true))
  else if decide (∃ j j' k k' : Fin n,
      ((j.1, k.1), (j'.1, k'.1)) ∈ G.2 ∧
      x = antiUnitPair k k' ∧ y = zeros2n ∧ z = unitPair j j') then
    some true
  else
    none

/-- **Ilango's `PartialMCSP` instance** [Ilango2020FOCS, Section III.B, p. 428; ECCC TR20-183,
Section 3, Theorem 11, pp. 20–21]: partial truth table $\gamma_G$ on $6n$ variables with size
threshold $s = 6n - 1$. -/
@[expose] def ilangoInstance (G : BipartitePermutationGraph) : Instance where
  arity := 6 * G.1
  table i := ilangoGamma G ((BitString.equivFin (6 * G.1)).symm i)
  threshold := 6 * G.1 - 1

@[simp] theorem ilangoInstance_arity (G : BipartitePermutationGraph) :
    (ilangoInstance G).arity = 6 * G.1 := rfl

@[simp] theorem ilangoInstance_threshold (G : BipartitePermutationGraph) :
    (ilangoInstance G).threshold = 6 * G.1 - 1 := rfl

@[simp] theorem ilangoInstance_partialFunction (G : BipartitePermutationGraph) :
    (ilangoInstance G).partialFunction = ilangoGamma G := by
  change (fun w : BitString (6 * G.1) =>
    (ilangoInstance G).table (BitString.equivFin (6 * G.1) w)) = ilangoGamma G
  funext w
  dsimp [ilangoInstance]
  rw [Equiv.symm_apply_apply]

/-! ### Evaluation of `ilangoGamma` on each of the seven clauses -/

/-- Clause (1): when $x = 0^{2n}$, $\gamma_G(0^{2n}, y, z) = \bigvee_i (y_i \wedge z_i)$. -/
@[simp] private theorem ilangoGamma_zeros2n_x (G : BipartitePermutationGraph)
    (y z : BitString (2 * G.1)) :
    ilangoGamma G (packXYZ zeros2n y z) =
      some (decide (∃ i : Fin (2 * G.1), y i = true ∧ z i = true)) := by
  simp [ilangoGamma]

/-- Clause (2): when $x = 1^{2n}$, $\gamma_G(1^{2n}, y, z) = \bigvee_i z_i$. -/
@[simp] private theorem ilangoGamma_ones2n_x (G : BipartitePermutationGraph)
    (y z : BitString (2 * G.1)) :
    ilangoGamma G (packXYZ ones2n y z) =
      some (decide (∃ i : Fin (2 * G.1), z i = true)) := by
  unfold ilangoGamma
  simp only [unpackX_packXYZ, unpackY_packXYZ, unpackZ_packXYZ, ite_true]
  split_ifs with h0
  · congr 2
    exact propext ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ =>
      ⟨i, by simpa using congrFun h0.symm i, hi⟩⟩
  · rfl

/-- Clause (3): when $z = 1^{2n}$, $\gamma_G(x, y, 1^{2n}) = \bigvee_i (x_i \vee y_i)$. -/
@[simp] private theorem ilangoGamma_ones2n_z (G : BipartitePermutationGraph)
    (x y : BitString (2 * G.1)) :
    ilangoGamma G (packXYZ x y ones2n) =
      some (decide (∃ i : Fin (2 * G.1), x i = true ∨ y i = true)) := by
  unfold ilangoGamma
  simp only [unpackX_packXYZ, unpackY_packXYZ, unpackZ_packXYZ]
  split_ifs with hx0 hx1
  · subst hx0; simp
  · subst hx1
    congr 2
    exact propext ⟨fun ⟨i, _⟩ => ⟨i, Or.inl rfl⟩, fun ⟨i, _⟩ => ⟨i, rfl⟩⟩
  · rfl

/-- Clause (4): when $z = 0^{2n}$, $\gamma_G(x, y, 0^{2n}) = 0$. -/
@[simp] private theorem ilangoGamma_zeros2n_z (G : BipartitePermutationGraph)
    (x y : BitString (2 * G.1)) :
    ilangoGamma G (packXYZ x y zeros2n) = some false := by
  unfold ilangoGamma
  simp only [unpackX_packXYZ, unpackY_packXYZ, unpackZ_packXYZ]
  split_ifs with hx0 hx1 hz1
  · simp
  · simp
  · congr 2
    simp only [decide_eq_false_iff_not, not_exists]
    intro i
    exact absurd (congrFun hz1 i) Bool.false_ne_true
  · rfl

/-- Clause (5): when $z = 1^n 0^n$ and $y = 0^{2n}$, $\gamma_G(x, 0^{2n}, 1^n 0^n) =
\bigvee_{i < n} x_i$. -/
@[simp] private theorem ilangoGamma_leftHalfOnes (G : BipartitePermutationGraph)
    (x : BitString (2 * G.1)) :
    ilangoGamma G (packXYZ x zeros2n leftHalfOnes) =
      some (decide (∃ i : Fin (2 * G.1), i.1 < G.1 ∧ x i = true)) := by
  unfold ilangoGamma
  simp only [unpackX_packXYZ, unpackY_packXYZ, unpackZ_packXYZ, and_true]
  split_ifs with hx0 hx1 hz1 hz0
  · subst hx0; congr 2; simp
  · subst hx1
    congr 2
    exact propext ⟨fun ⟨i, hi⟩ => ⟨i, by simpa [leftHalfOnes] using hi, rfl⟩,
      fun ⟨i, hi, _⟩ => ⟨i, by simpa [leftHalfOnes] using hi⟩⟩
  · congr 2
    exact propext ⟨fun ⟨i, hi⟩ => ⟨i, by simpa [leftHalfOnes] using congrFun hz1 i,
      by simpa using hi⟩, fun ⟨i, _, hi⟩ => ⟨i, Or.inl hi⟩⟩
  · simp only [Option.some.injEq, false_eq_decide_iff, not_exists, not_and]
    intro i hi _
    have := congrFun hz0 i
    revert this
    simp [leftHalfOnes, zeros2n, hi]
  · rfl

/-- Clause (6): when $z = 0^n 1^n$ and $y = 0^{2n}$, $\gamma_G(x, 0^{2n}, 0^n 1^n) =
\bigvee_{n \le i < 2n} x_i$. -/
@[simp] private theorem ilangoGamma_rightHalfOnes (G : BipartitePermutationGraph)
    (x : BitString (2 * G.1)) :
    ilangoGamma G (packXYZ x zeros2n rightHalfOnes) =
      some (decide (∃ i : Fin (2 * G.1), G.1 ≤ i.1 ∧ x i = true)) := by
  unfold ilangoGamma
  simp only [unpackX_packXYZ, unpackY_packXYZ, unpackZ_packXYZ, and_true]
  split_ifs with hx0 hx1 hz1 hz0 hleft
  · subst hx0; congr 2; simp
  · subst hx1
    congr 2
    exact propext ⟨fun ⟨i, hi⟩ => ⟨i, by simpa [rightHalfOnes] using hi, rfl⟩,
      fun ⟨i, hi, _⟩ => ⟨i, by simpa [rightHalfOnes] using hi⟩⟩
  · congr 2
    exact propext ⟨fun ⟨i, hi⟩ => ⟨i, by simpa [rightHalfOnes] using congrFun hz1 i,
      by simpa using hi⟩, fun ⟨i, _, hi⟩ => ⟨i, Or.inl hi⟩⟩
  · simp only [Option.some.injEq, false_eq_decide_iff, not_exists, not_and]
    intro i hi _
    have := congrFun hz0 i
    revert this
    simp [rightHalfOnes, zeros2n, hi]
  · rcases Nat.eq_zero_or_pos G.1 with h0 | hpos
    · congr 2
      exact propext ⟨fun ⟨i, _⟩ => absurd i.2 (by omega), fun ⟨i, _⟩ => absurd i.2 (by omega)⟩
    · exfalso
      have h0 : rightHalfOnes (⟨0, by omega⟩ : Fin (2 * G.1)) =
          leftHalfOnes (⟨0, by omega⟩ : Fin (2 * G.1)) := congrFun hleft _
      simp [rightHalfOnes, leftHalfOnes, hpos, Nat.not_le.mpr hpos] at h0
  · rfl

/-- Clause (7): for $2 \le G.1$ and any edge $((j, k), (j', k')) \in G.2$,
$\gamma_G(\overline{e_k}\,\overline{e_{k'}}, 0^{2n}, e_j\,e_{j'}) = 1$. -/
private theorem ilangoGamma_edge {G : BipartitePermutationGraph} (hn : 2 ≤ G.1)
    (j j' k k' : Fin G.1) (he : ((j.1, k.1), (j'.1, k'.1)) ∈ G.2) :
    ilangoGamma G (packXYZ (antiUnitPair k k') zeros2n (unitPair j j')) = some true := by
  unfold ilangoGamma
  simp only [unpackX_packXYZ, unpackY_packXYZ, unpackZ_packXYZ, and_true, true_and]
  have hx0 : antiUnitPair k k' ≠ zeros2n := fun h => by
    have hm := congrFun h ⟨1 - k.1, by omega⟩
    simp only [antiUnitPair, zeros2n, Bool.not_eq_false', decide_eq_true_eq] at hm
    omega
  have hx1 : antiUnitPair k k' ≠ ones2n := fun h => by
    simpa [antiUnitPair, ones2n] using congrFun h ⟨k.1, by omega⟩
  have hz1 : unitPair j j' ≠ ones2n := fun h => by
    have hm := congrFun h ⟨1 - j.1, by omega⟩
    simp only [unitPair, ones2n, decide_eq_true_eq] at hm
    omega
  have hz0 : unitPair j j' ≠ zeros2n := fun h => by
    simpa [unitPair, zeros2n] using congrFun h ⟨j.1, by omega⟩
  have hz_left : unitPair j j' ≠ leftHalfOnes := fun h => by
    simpa [unitPair, leftHalfOnes] using congrFun h ⟨G.1 + j'.1, by omega⟩
  have hz_right : unitPair j j' ≠ rightHalfOnes := fun h => by
    have hj := congrFun h ⟨j.1, by omega⟩
    simp only [unitPair, rightHalfOnes, true_or, decide_true, eq_comm (a := true),
      decide_eq_true_eq] at hj
    omega
  have hedge : decide (∃ j₁ j₁' k₁ k₁' : Fin G.1,
      ((j₁.1, k₁.1), (j₁'.1, k₁'.1)) ∈ G.2 ∧
      antiUnitPair k k' = antiUnitPair k₁ k₁' ∧
      unitPair j j' = unitPair j₁ j₁') = true :=
    decide_eq_true ⟨j, j', k, k', he, rfl, rfl⟩
  simp only [hx0, hx1, hz1, hz0, hz_left, hz_right, hedge, ↓reduceIte]

/-! ### Positive essentiality of all $6n$ variables (`Claim 13`) -/

@[simp] private theorem update_zeros2n_false (i : Fin (2 * n)) :
    Function.update (zeros2n (n := n)) i false = zeros2n :=
  Function.update_eq_self i zeros2n

/-- **Claim 13** [ECCC TR20-183, Section 3, p. 24]: when $1 \le G.1$, every variable $v \in
\mathrm{Fin}\,(6n)$ is positively essential for any total function $f$ agreeing with
`ilangoInstance G`. -/
private theorem ilangoInstance_posEssential {G : BipartitePermutationGraph} (_hn : 0 < G.1)
    {f : BitString (6 * G.1) → Bool} (hf : (ilangoInstance G).AgreesWith f)
    (v : Fin (6 * G.1)) :
    ∃ w : BitString (6 * G.1),
      f (Function.update w v false) = false ∧ f (Function.update w v true) = true := by
  rcases eq_xVar_or_yVar_or_zVar v with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨packXYZ zeros2n zeros2n ones2n, ?_, ?_⟩
    · rw [update_packXYZ_xVar, update_zeros2n_false]
      exact hf _ false (by simp)
    · rw [update_packXYZ_xVar]
      refine hf _ true ?_
      rw [ilangoInstance_partialFunction, ilangoGamma_ones2n_z]
      simp only [Option.some.injEq, decide_eq_true_iff]
      exact ⟨i, Or.inl (by simp)⟩
  · refine ⟨packXYZ zeros2n zeros2n ones2n, ?_, ?_⟩
    · rw [update_packXYZ_yVar, update_zeros2n_false]
      exact hf _ false (by simp)
    · rw [update_packXYZ_yVar]
      refine hf _ true ?_
      rw [ilangoInstance_partialFunction, ilangoGamma_ones2n_z]
      simp only [Option.some.injEq, decide_eq_true_iff]
      exact ⟨i, Or.inr (by simp)⟩
  · refine ⟨packXYZ ones2n zeros2n zeros2n, ?_, ?_⟩
    · rw [update_packXYZ_zVar, update_zeros2n_false]
      exact hf _ false (by simp)
    · rw [update_packXYZ_zVar]
      refine hf _ true ?_
      rw [ilangoInstance_partialFunction, ilangoGamma_ones2n_x]
      simp only [Option.some.injEq, decide_eq_true_iff]
      exact ⟨i, by simp⟩

/-! ### Ilango's Lemma 12: Structural characterization of read-once formulas for Clauses 1–4 -/

/-- The finset of `x`-coordinates in `Fin (6 * n)`. -/
private def xSet (n : ℕ) : Finset (Fin (6 * n)) :=
  Finset.univ.image xVar

/-- The finset of `y`-coordinates in `Fin (6 * n)`. -/
private def ySet (n : ℕ) : Finset (Fin (6 * n)) :=
  Finset.univ.image yVar

@[simp] private theorem mem_xSet {v : Fin (6 * n)} : v ∈ xSet n ↔ ∃ i, v = xVar i := by
  simp [xSet, eq_comm]

@[simp] private theorem mem_ySet {v : Fin (6 * n)} : v ∈ ySet n ↔ ∃ i, v = yVar i := by
  simp [ySet, eq_comm]

@[simp] private theorem card_xSet (n : ℕ) : (xSet n).card = 2 * n := by
  rw [xSet, Finset.card_image_of_injective _ xVar_injective, Finset.card_univ, Fintype.card_fin]

@[simp] private theorem card_ySet (n : ℕ) : (ySet n).card = 2 * n := by
  rw [ySet, Finset.card_image_of_injective _ yVar_injective, Finset.card_univ, Fintype.card_fin]

private theorem disjoint_xSet_ySet (n : ℕ) : Disjoint (xSet n) (ySet n) := by
  rw [Finset.disjoint_left]
  intro v hvx hvy
  obtain ⟨i, rfl⟩ := mem_xSet.mp hvx
  obtain ⟨j, hj⟩ := mem_ySet.mp hvy
  exact xVar_ne_yVar i j hj

/-- **Claim 14** [ECCC TR20-183, Section 3, p. 25]: any read-once positive formula `F` on $6n$
variables with `F.leafSize = 6 * n` agreeing with Clause (3) has `4 * n ≤ F.numOr + 1` and
`F.numAnd ≤ 2 * n`. -/
private theorem numAnd_le_two_mul_of_clause3 {F : PosFormula (6 * n)} (hro : F.IsReadOnce)
    (hleaf : F.leafSize = 6 * n)
    (hC3 : ∀ x y : BitString (2 * n),
      F.eval (packXYZ x y ones2n) = decide (∃ i, x i = true ∨ y i = true)) :
    4 * n ≤ F.numOr + 1 ∧ F.numAnd ≤ 2 * n := by
  have hsupp : F.leafSupport = Finset.univ := by
    have hcard : F.leafSupport.card = 6 * n :=
      ((F.isReadOnce_iff_card_leafSupport_eq_leafSize).mp hro).trans hleaf
    exact Finset.eq_univ_of_card F.leafSupport (by simpa using hcard)
  let w₀ : BitString (6 * n) := packXYZ zeros2n zeros2n ones2n
  have hw₀ : F.eval w₀ = false := by
    simpa [w₀] using hC3 zeros2n zeros2n
  have hsub : xSet n ∪ ySet n ⊆ PosFormula.flipSensitive w₀ F := by
    intro v hv
    simp only [PosFormula.flipSensitive, hsupp, Finset.mem_filter, Finset.mem_univ, hw₀,
      Bool.not_false, Bool.true_and, true_and]
    rcases Finset.mem_union.mp hv with hvx | hvy
    · obtain ⟨i, rfl⟩ := mem_xSet.mp hvx
      rw [show Function.update w₀ (xVar i) true =
          packXYZ (Function.update zeros2n i true) zeros2n ones2n from
        update_packXYZ_xVar _ _ _ i true, hC3, decide_eq_true_iff]
      exact ⟨i, Or.inl (by simp)⟩
    · obtain ⟨i, rfl⟩ := mem_ySet.mp hvy
      rw [show Function.update w₀ (yVar i) true =
          packXYZ zeros2n (Function.update zeros2n i true) ones2n from
        update_packXYZ_yVar _ _ _ i true, hC3, decide_eq_true_iff]
      exact ⟨i, Or.inr (by simp)⟩
  have hcard_xy : (xSet n ∪ ySet n).card = 4 * n := by
    rw [Finset.card_union_of_disjoint (disjoint_xSet_ySet n), card_xSet, card_ySet]
    omega
  have hor : 4 * n ≤ F.numOr + 1 := by
    calc 4 * n = (xSet n ∪ ySet n).card := hcard_xy.symm
      _ ≤ (PosFormula.flipSensitive w₀ F).card := Finset.card_le_card hsub
      _ ≤ F.numOr + 1 := PosFormula.card_flipSensitive_le_numOr_add_one w₀ hro
  have hsum := F.numAnd_add_numOr_add_one
  omega

/-- For any `i : Fin (2 * n)` and any coordinate `u ≠ zVar i`, Clauses (1) and (3) provide an input
`w` with `w (zVar i) = true` on which flipping `u` from `false` to `true` flips `F.eval` from
`false` to `true`. -/
private theorem exists_flip_with_zVar_true {F : PosFormula (6 * n)}
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ j, y j = true ∧ z j = true))
    (hC3 : ∀ x y : BitString (2 * n),
      F.eval (packXYZ x y ones2n) = decide (∃ j, x j = true ∨ y j = true))
    (i : Fin (2 * n)) {u : Fin (6 * n)} (hu : u ≠ zVar i) :
    ∃ w : BitString (6 * n),
      w (zVar i) = true ∧
      F.eval (Function.update w u false) = false ∧
      F.eval (Function.update w u true) = true := by
  rcases eq_xVar_or_yVar_or_zVar u with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · refine ⟨packXYZ zeros2n zeros2n ones2n, by simp, ?_, ?_⟩
    · rw [update_packXYZ_xVar, update_zeros2n_false, hC3]
      simp
    · rw [update_packXYZ_xVar, hC3, decide_eq_true_iff]
      exact ⟨j, Or.inl (by simp)⟩
  · refine ⟨packXYZ zeros2n zeros2n ones2n, by simp, ?_, ?_⟩
    · rw [update_packXYZ_yVar, update_zeros2n_false, hC3]
      simp
    · rw [update_packXYZ_yVar, hC3, decide_eq_true_iff]
      exact ⟨j, Or.inr (by simp)⟩
  · have hji : j ≠ i := zVar_inj.not.mp hu
    let y₀ := Function.update (zeros2n (n := n)) j true
    let z₀ := Function.update (zeros2n (n := n)) i true
    refine ⟨packXYZ zeros2n y₀ z₀, by simp [z₀], ?_, ?_⟩
    · have hz_upd : Function.update z₀ j false = z₀ := by
        apply Function.update_eq_self_iff.mpr
        simp [z₀, Function.update_of_ne hji]
      rw [update_packXYZ_zVar, hz_upd, hC1, decide_eq_false_iff_not]
      rintro ⟨k, hk_y, hk_z⟩
      by_cases hkj : k = j
      · subst hkj
        simp [z₀, Function.update_of_ne hji] at hk_z
      · simp [y₀, Function.update_of_ne hkj] at hk_y
    · rw [update_packXYZ_zVar, hC1, decide_eq_true_iff]
      exact ⟨j, by simp [y₀], by simp⟩

/-- **Claim 15 (left)** [ECCC TR20-183, Section 3, p. 25]: no `zVar i` leaf is the left child of an
`or` subformula of `F`. -/
private theorem not_isSubformula_or_var_zVar_left {F : PosFormula (6 * n)} (hro : F.IsReadOnce)
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ j, y j = true ∧ z j = true))
    (hC3 : ∀ x y : BitString (2 * n),
      F.eval (packXYZ x y ones2n) = decide (∃ j, x j = true ∨ y j = true))
    (i : Fin (2 * n)) (A : PosFormula (6 * n)) :
    ¬PosFormula.IsSubformula (.or (.var (zVar i)) A) F := by
  intro hsub
  obtain ⟨u, huA⟩ := A.leafSupport_nonempty
  have hroT := hsub.isReadOnce hro
  have hu_ne : u ≠ zVar i := by
    intro h
    subst h
    exact Finset.disjoint_left.mp hroT.2.2 (Finset.mem_singleton_self _) huA
  obtain ⟨w, hwz, hf0, hf1⟩ := exists_flip_with_zVar_true hC1 hC3 i hu_ne
  let w₀ := Function.update w u false
  let w₁ := Function.update w u true
  have hw₀z : w₀ (zVar i) = true := by
    simpa [w₀, Function.update_of_ne hu_ne.symm] using hwz
  have hw₁z : w₁ (zVar i) = true := by
    simpa [w₁, Function.update_of_ne hu_ne.symm] using hwz
  have heq : F.eval w₀ = F.eval w₁ := by
    refine PosFormula.eval_eq_of_isSubformula_of_eval_eq hsub hro (fun v hv => ?_) ?_
    · have hvu : v ≠ u := fun h => hv (Finset.mem_union_right _ (h ▸ huA))
      simp [w₀, w₁, Function.update_of_ne hvu]
    · simp [hw₀z, hw₁z]
  exact Bool.false_ne_true (hf0.symm.trans (heq.trans hf1))

/-- **Claim 15 (right)** [ECCC TR20-183, Section 3, p. 25]: no `zVar i` leaf is the right child of
an `or` subformula of `F`. -/
private theorem not_isSubformula_or_var_zVar_right {F : PosFormula (6 * n)} (hro : F.IsReadOnce)
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ j, y j = true ∧ z j = true))
    (hC3 : ∀ x y : BitString (2 * n),
      F.eval (packXYZ x y ones2n) = decide (∃ j, x j = true ∨ y j = true))
    (i : Fin (2 * n)) (A : PosFormula (6 * n)) :
    ¬PosFormula.IsSubformula (.or A (.var (zVar i))) F := by
  intro hsub
  obtain ⟨u, huA⟩ := A.leafSupport_nonempty
  have hroT := hsub.isReadOnce hro
  have hu_ne : u ≠ zVar i := by
    intro h
    subst h
    exact Finset.disjoint_right.mp hroT.2.2 (Finset.mem_singleton_self _) huA
  obtain ⟨w, hwz, hf0, hf1⟩ := exists_flip_with_zVar_true hC1 hC3 i hu_ne
  let w₀ := Function.update w u false
  let w₁ := Function.update w u true
  have hw₀z : w₀ (zVar i) = true := by
    simpa [w₀, Function.update_of_ne hu_ne.symm] using hwz
  have hw₁z : w₁ (zVar i) = true := by
    simpa [w₁, Function.update_of_ne hu_ne.symm] using hwz
  have heq : F.eval w₀ = F.eval w₁ := by
    refine PosFormula.eval_eq_of_isSubformula_of_eval_eq hsub hro (fun v hv => ?_) ?_
    · have hvu : v ≠ u := fun h => hv (Finset.mem_union_left _ (h ▸ huA))
      simp [w₀, w₁, Function.update_of_ne hvu]
    · simp [hw₀z, hw₁z]
  exact Bool.false_ne_true (hf0.symm.trans (heq.trans hf1))

/-- **Claim 16 (left)** [ECCC TR20-183, Section 3, p. 25]: if `.and (.var (zVar i)) A` is a
subformula of `F`, then `A` reads no `z`-variable (`∀ j, zVar j ∉ A.leafSupport`). -/
private theorem not_mem_leafSupport_zVar_of_isSubformula_and_left {F : PosFormula (6 * n)}
    (hro : F.IsReadOnce)
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ j, y j = true ∧ z j = true))
    {i j : Fin (2 * n)} {A : PosFormula (6 * n)}
    (hsub : PosFormula.IsSubformula (.and (.var (zVar i)) A) F) :
    zVar j ∉ A.leafSupport := by
  intro hjA
  have hroT := hsub.isReadOnce hro
  have hji : j ≠ i := by
    intro h
    subst h
    exact Finset.disjoint_left.mp hroT.2.2 (Finset.mem_singleton_self _) hjA
  let y₀ := Function.update (zeros2n (n := n)) j true
  let w₀ := packXYZ zeros2n y₀ zeros2n
  let w₁ := Function.update w₀ (zVar j) true
  have hw₀i : w₀ (zVar i) = false := by simp [w₀]
  have hw₁i : w₁ (zVar i) = false := by
    simp [w₁, w₀, Function.update_of_ne (zVar_inj.not.mpr hji.symm)]
  have heq : F.eval w₀ = F.eval w₁ := by
    refine PosFormula.eval_eq_of_isSubformula_of_eval_eq hsub hro (fun v hv => ?_) ?_
    · have hvj : v ≠ zVar j := fun h => hv (Finset.mem_union_right _ (h ▸ hjA))
      simp [w₁, Function.update_of_ne hvj]
    · simp [hw₀i, hw₁i]
  have hf₀ : F.eval w₀ = false := by
    simpa [w₀] using hC1 y₀ zeros2n
  have hf₁ : F.eval w₁ = true := by
    rw [show w₁ = packXYZ zeros2n y₀ (Function.update zeros2n j true) from
      update_packXYZ_zVar _ _ _ j true, hC1, decide_eq_true_iff]
    exact ⟨j, by simp [y₀], by simp⟩
  exact Bool.false_ne_true (hf₀.symm.trans (heq.trans hf₁))

/-- **Claim 16 (right)** [ECCC TR20-183, Section 3, p. 25]: if `.and A (.var (zVar i))` is a
subformula of `F`, then `A` reads no `z`-variable (`∀ j, zVar j ∉ A.leafSupport`). -/
private theorem not_mem_leafSupport_zVar_of_isSubformula_and_right {F : PosFormula (6 * n)}
    (hro : F.IsReadOnce)
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ j, y j = true ∧ z j = true))
    {i j : Fin (2 * n)} {A : PosFormula (6 * n)}
    (hsub : PosFormula.IsSubformula (.and A (.var (zVar i))) F) :
    zVar j ∉ A.leafSupport := by
  intro hjA
  have hroT := hsub.isReadOnce hro
  have hji : j ≠ i := by
    intro h
    subst h
    exact Finset.disjoint_right.mp hroT.2.2 (Finset.mem_singleton_self _) hjA
  let y₀ := Function.update (zeros2n (n := n)) j true
  let w₀ := packXYZ zeros2n y₀ zeros2n
  let w₁ := Function.update w₀ (zVar j) true
  have hw₀i : w₀ (zVar i) = false := by simp [w₀]
  have hw₁i : w₁ (zVar i) = false := by
    simp [w₁, w₀, Function.update_of_ne (zVar_inj.not.mpr hji.symm)]
  have heq : F.eval w₀ = F.eval w₁ := by
    refine PosFormula.eval_eq_of_isSubformula_of_eval_eq hsub hro (fun v hv => ?_) ?_
    · have hvj : v ≠ zVar j := fun h => hv (Finset.mem_union_left _ (h ▸ hjA))
      simp [w₁, Function.update_of_ne hvj]
    · simp [hw₀i, hw₁i]
  have hf₀ : F.eval w₀ = false := by
    simpa [w₀] using hC1 y₀ zeros2n
  have hf₁ : F.eval w₁ = true := by
    rw [show w₁ = packXYZ zeros2n y₀ (Function.update zeros2n j true) from
      update_packXYZ_zVar _ _ _ j true, hC1, decide_eq_true_iff]
    exact ⟨j, by simp [y₀], by simp⟩
  exact Bool.false_ne_true (hf₀.symm.trans (heq.trans hf₁))

/-- Number of `z`-variables in `S.leafSupport`. -/
private def zCount (S : PosFormula (6 * n)) : ℕ :=
  (S.leafSupport ∩ zSet n).card

/-- Predicate stating that `S` is not a bare `z`-variable leaf `.var (zVar i)`. -/
private def NotZLeaf (S : PosFormula (6 * n)) : Prop :=
  ∀ i : Fin (2 * n), S ≠ .var (zVar i)

@[simp] private theorem zCount_var_zVar (i : Fin (2 * n)) :
    zCount (.var (zVar i) : PosFormula (6 * n)) = 1 := by
  have : ({zVar i} ∩ zSet n : Finset (Fin (6 * n))) = {zVar i} :=
    Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr (zVar_mem_zSet i))
  simp [zCount, this]

private theorem zCount_var_of_notZLeaf {v : Fin (6 * n)}
    (h : NotZLeaf (.var v : PosFormula (6 * n))) :
    zCount (.var v) = 0 := by
  have hv : v ∉ zSet n := by
    rw [mem_zSet]
    rintro ⟨i, rfl⟩
    exact h i rfl
  have : ({v} ∩ zSet n : Finset (Fin (6 * n))) = ∅ :=
    Finset.singleton_inter_of_notMem hv
  simp [zCount, this]

private theorem zCount_union_of_disjoint {L R : PosFormula (6 * n)}
    (hdisj : Disjoint L.leafSupport R.leafSupport) :
    ((L.leafSupport ∪ R.leafSupport) ∩ zSet n).card = zCount L + zCount R := by
  rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint]
  · rfl
  · exact hdisj.mono Finset.inter_subset_left Finset.inter_subset_left

private theorem zCount_and_of_isReadOnce {L R : PosFormula (6 * n)}
    (hro : (PosFormula.and L R).IsReadOnce) :
    zCount (.and L R) = zCount L + zCount R :=
  zCount_union_of_disjoint hro.2.2

private theorem zCount_or_of_isReadOnce {L R : PosFormula (6 * n)}
    (hro : (PosFormula.or L R).IsReadOnce) :
    zCount (.or L R) = zCount L + zCount R :=
  zCount_union_of_disjoint hro.2.2

private theorem disjoint_leafSupport_zSet_of_forall_notMem {A : PosFormula (6 * n)}
    (h : ∀ j, zVar j ∉ A.leafSupport) :
    Disjoint A.leafSupport (zSet n) ∧ zCount A = 0 := by
  have hdisj : Disjoint A.leafSupport (zSet n) := by
    rw [Finset.disjoint_left]
    rintro v hvA hvz
    obtain ⟨j, rfl⟩ := mem_zSet.mp hvz
    exact h j hvA
  exact ⟨hdisj, Finset.card_eq_zero.mpr (Finset.disjoint_iff_inter_eq_empty.mp hdisj)⟩

/-- Every subformula `S` of `F` that is not a single `z`-leaf satisfies `zCount S ≤ S.numAnd`. -/
private theorem zCount_le_numAnd_of_notZLeaf {F S : PosFormula (6 * n)} (hro : F.IsReadOnce)
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ j, y j = true ∧ z j = true))
    (hC3 : ∀ x y : BitString (2 * n),
      F.eval (packXYZ x y ones2n) = decide (∃ j, x j = true ∨ y j = true))
    (hsub : PosFormula.IsSubformula S F) (hnotZ : NotZLeaf S) :
    zCount S ≤ S.numAnd := by
  induction S with
  | var v =>
    rw [zCount_var_of_notZLeaf hnotZ, PosFormula.numAnd_var]
  | or L R ihL ihR =>
    have hnotZL : NotZLeaf L := fun i hL =>
      not_isSubformula_or_var_zVar_left hro hC1 hC3 i R (hL ▸ hsub)
    have hnotZR : NotZLeaf R := fun i hR =>
      not_isSubformula_or_var_zVar_right hro hC1 hC3 i L (hR ▸ hsub)
    have hL := ihL hsub.of_or_left hnotZL
    have hR := ihR hsub.of_or_right hnotZR
    rw [zCount_or_of_isReadOnce (hsub.isReadOnce hro), PosFormula.numAnd_or]
    omega
  | and L R ihL ihR =>
    rw [zCount_and_of_isReadOnce (hsub.isReadOnce hro), PosFormula.numAnd_and]
    by_cases hL : ∃ i, L = .var (zVar i)
    · obtain ⟨i, rfl⟩ := hL
      have hR0 := (disjoint_leafSupport_zSet_of_forall_notMem fun j =>
        not_mem_leafSupport_zVar_of_isSubformula_and_left hro hC1 hsub).2
      rw [zCount_var_zVar, hR0]
      omega
    · by_cases hR : ∃ i, R = .var (zVar i)
      · obtain ⟨i, rfl⟩ := hR
        have hL0 := (disjoint_leafSupport_zSet_of_forall_notMem fun j =>
          not_mem_leafSupport_zVar_of_isSubformula_and_right hro hC1 hsub).2
        rw [zCount_var_zVar, hL0]
        omega
      · have hL_le := ihL hsub.of_and_left fun i hi => hL ⟨i, hi⟩
        have hR_le := ihR hsub.of_and_right fun i hi => hR ⟨i, hi⟩
        omega

/-- Variables appearing above all `and` gates in `S` (the set $I$ in Claim 17 of
[ECCC TR20-183, p. 25]). -/
private def topOrVars : PosFormula (6 * n) → Finset (Fin (6 * n))
  | .var v => {v}
  | .or L R => topOrVars L ∪ topOrVars R
  | .and _ _ => ∅

/-- Variables paired with `zVar i` inside an `and` gate of `S` (the set $I_i$ in
[ECCC TR20-183, p. 26]). -/
private def zPartnerVars (i : Fin (2 * n)) : PosFormula (6 * n) → Finset (Fin (6 * n))
  | .var _ => ∅
  | .or L R => zPartnerVars i L ∪ zPartnerVars i R
  | .and L R =>
    if L = .var (zVar i) then R.leafSupport
    else if R = .var (zVar i) then L.leafSupport
    else ∅

private theorem zPartnerVars_subset_leafSupport (i : Fin (2 * n)) (S : PosFormula (6 * n)) :
    zPartnerVars i S ⊆ S.leafSupport := by
  induction S with
  | var _ => exact Finset.empty_subset _
  | or L R ihL ihR => exact Finset.union_subset_union ihL ihR
  | and L R =>
    dsimp [zPartnerVars]
    split_ifs
    · exact Finset.subset_union_right
    · exact Finset.subset_union_left
    · exact Finset.empty_subset _

/-- Structural decomposition of a subformula `S` of `F` into top-level `or`-variables
`topOrVars S` and `z`-partner variable sets `zPartnerVars i S`
[ECCC TR20-183, Section 3, pp. 25–26]. -/
private structure ZDecomp (S : PosFormula (6 * n)) : Prop where
  disjoint_top : Disjoint (topOrVars S) (zSet n)
  disjoint_partner : ∀ i, Disjoint (zPartnerVars i S) (zSet n)
  disjoint_ij : ∀ i j, i ≠ j → Disjoint (zPartnerVars i S) (zPartnerVars j S)
  eval_eq : ∀ w : BitString (6 * n),
    S.eval w =
      decide ((∃ v ∈ topOrVars S, w v = true) ∨
        (∃ i : Fin (2 * n), w (zVar i) = true ∧ ∃ v ∈ zPartnerVars i S, w v = true))

private theorem ZDecomp.of_or {L R : PosFormula (6 * n)}
    (hroS : (PosFormula.or L R).IsReadOnce) (hL : ZDecomp L) (hR : ZDecomp R) :
    ZDecomp (.or L R) where
  disjoint_top := Finset.disjoint_union_left.mpr ⟨hL.disjoint_top, hR.disjoint_top⟩
  disjoint_partner i :=
    Finset.disjoint_union_left.mpr ⟨hL.disjoint_partner i, hR.disjoint_partner i⟩
  disjoint_ij i j hij := by
    have hLR := hroS.2.2.mono
      (zPartnerVars_subset_leafSupport i L) (zPartnerVars_subset_leafSupport j R)
    have hRL := hroS.2.2.symm.mono
      (zPartnerVars_subset_leafSupport i R) (zPartnerVars_subset_leafSupport j L)
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hL.disjoint_ij i j hij, hLR⟩,
        Finset.disjoint_union_right.mpr ⟨hRL, hR.disjoint_ij i j hij⟩⟩
  eval_eq w := by
    rw [PosFormula.eval_or, hL.eval_eq w, hR.eval_eq w, ← Bool.decide_or, decide_eq_decide]
    simp only [topOrVars, zPartnerVars, Finset.mem_union]
    exact ⟨fun
      | .inl (.inl ⟨v, hv, hw⟩) => .inl ⟨v, .inl hv, hw⟩
      | .inl (.inr ⟨i, hi, v, hv, hw⟩) => .inr ⟨i, hi, v, .inl hv, hw⟩
      | .inr (.inl ⟨v, hv, hw⟩) => .inl ⟨v, .inr hv, hw⟩
      | .inr (.inr ⟨i, hi, v, hv, hw⟩) => .inr ⟨i, hi, v, .inr hv, hw⟩,
    fun
      | .inl ⟨v, .inl hv, hw⟩ => .inl (.inl ⟨v, hv, hw⟩)
      | .inl ⟨v, .inr hv, hw⟩ => .inr (.inl ⟨v, hv, hw⟩)
      | .inr ⟨i, hi, v, .inl hv, hw⟩ => .inl (.inr ⟨i, hi, v, hv, hw⟩)
      | .inr ⟨i, hi, v, .inr hv, hw⟩ => .inr (.inr ⟨i, hi, v, hv, hw⟩)⟩

private theorem ZDecomp.of_single_zPartner {S A : PosFormula (6 * n)} {i₀ : Fin (2 * n)}
    (htop : topOrVars S = ∅)
    (hpart : ∀ i, zPartnerVars i S = if i = i₀ then A.leafSupport else ∅)
    (hdisj : Disjoint A.leafSupport (zSet n)) (hand0 : A.numAnd = 0)
    (heval : ∀ w : BitString (6 * n), S.eval w = (w (zVar i₀) && A.eval w)) :
    ZDecomp S where
  disjoint_top := htop ▸ Finset.disjoint_empty_left _
  disjoint_partner i := by
    rw [hpart i]
    split_ifs
    · exact hdisj
    · exact Finset.disjoint_empty_left _
  disjoint_ij i j hij := by
    rw [hpart i, hpart j]
    split_ifs with hi hj
    · exact absurd (hi.trans hj.symm) hij
    · exact Finset.disjoint_empty_right _
    · exact Finset.disjoint_empty_left _
    · exact Finset.disjoint_empty_left _
  eval_eq w := by
    rw [heval w, PosFormula.eval_eq_decide_exists_of_numAnd_eq_zero hand0 w]
    simp only [htop, Finset.notMem_empty, false_and, exists_false, false_or, hpart]
    rw [← Bool.decide_coe (w (zVar i₀)), ← Bool.decide_and, decide_eq_decide]
    refine ⟨fun ⟨hwz, v, hv, hwv⟩ => ⟨i₀, hwz, v, by simp [hv], hwv⟩, ?_⟩
    rintro ⟨i, hwz, v, hv, hwv⟩
    by_cases hi : i = i₀
    · subst hi
      exact ⟨hwz, v, by simpa using hv, hwv⟩
    · simp [hi] at hv

private theorem zPartnerVars_and_var_left {R : PosFormula (6 * n)} {i₀ i : Fin (2 * n)}
    (hdisj : Disjoint R.leafSupport (zSet n)) :
    zPartnerVars i (.and (.var (zVar i₀)) R) = if i = i₀ then R.leafSupport else ∅ := by
  dsimp [zPartnerVars]
  have hneR : R ≠ .var (zVar i) := by
    rintro rfl
    exact Finset.disjoint_left.mp hdisj (Finset.mem_singleton_self _) (zVar_mem_zSet i)
  by_cases hi : i = i₀
  · subst hi; simp
  · simp [hi, Ne.symm hi, hneR]

private theorem zPartnerVars_and_var_right {L : PosFormula (6 * n)} {i₀ i : Fin (2 * n)}
    (hdisj : Disjoint L.leafSupport (zSet n)) :
    zPartnerVars i (.and L (.var (zVar i₀))) = if i = i₀ then L.leafSupport else ∅ := by
  dsimp [zPartnerVars]
  have hneL : L ≠ .var (zVar i) := by
    rintro rfl
    exact Finset.disjoint_left.mp hdisj (Finset.mem_singleton_self _) (zVar_mem_zSet i)
  by_cases hi : i = i₀
  · subst hi; simp [hneL]
  · simp [hi, Ne.symm hi, hneL]

/-- Structural decomposition of any subformula `S` of `F` satisfying `NotZLeaf S` and
`zCount S = S.numAnd` [ECCC TR20-183, Section 3, pp. 25–26]. -/
private theorem structure_of_zCount_eq_numAnd {F S : PosFormula (6 * n)} (hro : F.IsReadOnce)
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ j, y j = true ∧ z j = true))
    (hC3 : ∀ x y : BitString (2 * n),
      F.eval (packXYZ x y ones2n) = decide (∃ j, x j = true ∨ y j = true))
    (hsub : PosFormula.IsSubformula S F) (hnotZ : NotZLeaf S) (hz : zCount S = S.numAnd) :
    ZDecomp S := by
  induction S with
  | var v =>
    refine ⟨?_, fun _ => Finset.disjoint_empty_left _, fun _ _ _ => Finset.disjoint_empty_left _,
      fun w => by simp [topOrVars, zPartnerVars]⟩
    rw [topOrVars, Finset.disjoint_singleton_left, mem_zSet]
    rintro ⟨i, rfl⟩
    exact hnotZ i rfl
  | or L R ihL ihR =>
    have hroS := hsub.isReadOnce hro
    have hnotZL : NotZLeaf L := fun i hL =>
      not_isSubformula_or_var_zVar_left hro hC1 hC3 i R (hL ▸ hsub)
    have hnotZR : NotZLeaf R := fun i hR =>
      not_isSubformula_or_var_zVar_right hro hC1 hC3 i L (hR ▸ hsub)
    have hL_le := zCount_le_numAnd_of_notZLeaf hro hC1 hC3 hsub.of_or_left hnotZL
    have hR_le := zCount_le_numAnd_of_notZLeaf hro hC1 hC3 hsub.of_or_right hnotZR
    rw [zCount_or_of_isReadOnce hroS, PosFormula.numAnd_or] at hz
    exact ZDecomp.of_or hroS
      (ihL hsub.of_or_left hnotZL (by omega)) (ihR hsub.of_or_right hnotZR (by omega))
  | and L R _ _ =>
    rw [zCount_and_of_isReadOnce (hsub.isReadOnce hro), PosFormula.numAnd_and] at hz
    have h_has_z : (∃ i, L = .var (zVar i)) ∨ (∃ i, R = .var (zVar i)) := by
      by_contra! h
      have hL_le := zCount_le_numAnd_of_notZLeaf hro hC1 hC3 hsub.of_and_left h.1
      have hR_le := zCount_le_numAnd_of_notZLeaf hro hC1 hC3 hsub.of_and_right h.2
      omega
    rcases h_has_z with ⟨i₀, rfl⟩ | ⟨i₀, rfl⟩
    · obtain ⟨hR_disj, hR_z0⟩ := disjoint_leafSupport_zSet_of_forall_notMem fun j =>
        not_mem_leafSupport_zVar_of_isSubformula_and_left hro hC1 hsub
      rw [zCount_var_zVar, hR_z0, PosFormula.numAnd_var] at hz
      exact ZDecomp.of_single_zPartner rfl (fun _ => zPartnerVars_and_var_left hR_disj)
        hR_disj (by omega) fun _ => rfl
    · obtain ⟨hL_disj, hL_z0⟩ := disjoint_leafSupport_zSet_of_forall_notMem fun j =>
        not_mem_leafSupport_zVar_of_isSubformula_and_right hro hC1 hsub
      rw [zCount_var_zVar, hL_z0, PosFormula.numAnd_var] at hz
      exact ZDecomp.of_single_zPartner rfl (fun _ => zPartnerVars_and_var_right hL_disj)
        hL_disj (by omega) fun w => Bool.and_comm _ _

/-- **Claim 17** [ECCC TR20-183, Section 3, p. 25]: under `ZDecomp F` and Clause (4),
`topOrVars F = ∅`, so `F.eval (packXYZ x y z)` is determined by the partner sets
`zPartnerVars i F`. -/
private theorem ZDecomp.eval_packXYZ_of_clause4 {F : PosFormula (6 * n)} (hd : ZDecomp F)
    (hC4 : ∀ x y : BitString (2 * n), F.eval (packXYZ x y zeros2n) = false) :
    (∀ x y z : BitString (2 * n),
      F.eval (packXYZ x y z) =
        decide (∃ i : Fin (2 * n), z i = true ∧
          ∃ v ∈ zPartnerVars i F, packXYZ x y z v = true)) ∧
    (∀ x y : BitString (2 * n), ∀ i : Fin (2 * n),
      F.eval (packXYZ x y (Function.update zeros2n i true)) =
        decide (∃ v ∈ zPartnerVars i F,
          packXYZ x y (Function.update zeros2n i true) v = true)) := by
  have htop_empty : topOrVars F = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have hv_notZ : v ∉ zSet n := Finset.disjoint_left.mp hd.disjoint_top hv
    have hwv : packXYZ ones2n ones2n zeros2n v = true := by
      rcases eq_xVar_or_yVar_or_zVar v with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · simp
      · simp
      · exact absurd (zVar_mem_zSet i) hv_notZ
    have h1 : F.eval (packXYZ ones2n ones2n zeros2n) = true := by
      rw [hd.eval_eq, decide_eq_true_iff]
      exact Or.inl ⟨v, hv, hwv⟩
    exact Bool.false_ne_true ((hC4 ones2n ones2n).symm.trans h1)
  have heval' (x y z : BitString (2 * n)) :
      F.eval (packXYZ x y z) =
        decide (∃ i : Fin (2 * n), z i = true ∧
          ∃ v ∈ zPartnerVars i F, packXYZ x y z v = true) := by
    simpa [htop_empty] using hd.eval_eq (packXYZ x y z)
  refine ⟨heval', fun x y i => ?_⟩
  rw [heval', decide_eq_decide]
  refine ⟨?_, fun ⟨v, hv, hwv⟩ => ⟨i, by simp, v, hv, hwv⟩⟩
  rintro ⟨j, hj, v, hv, hwv⟩
  have hji : j = i := by
    by_contra hne
    simp [Function.update_of_ne hne] at hj
  exact ⟨v, hji ▸ hv, hwv⟩

private theorem exists_perm_and_mem_iff_of_disjoint
    {P : Fin (2 * n) → Finset (Fin (6 * n))}
    (hd_ij : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    {var : Fin (2 * n) → Fin (6 * n)}
    (hex : ∀ i, ∃ k, var k ∈ P i) :
    ∃ π : Equiv.Perm (Fin (2 * n)), ∀ i k, var k ∈ P i ↔ k = π i := by
  let f (i : Fin (2 * n)) : Fin (2 * n) := (hex i).choose
  have hf_mem (i : Fin (2 * n)) : var (f i) ∈ P i := (hex i).choose_spec
  have hf_inj : Function.Injective f := fun i j hij => by
    by_contra hne
    exact Finset.disjoint_left.mp (hd_ij i j hne) (hf_mem i) (hij ▸ hf_mem j)
  let π : Equiv.Perm (Fin (2 * n)) :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hπ_mem (i : Fin (2 * n)) : var (π i) ∈ P i := hf_mem i
  refine ⟨π, fun i k => ⟨fun hk => ?_, fun h => h ▸ hπ_mem i⟩⟩
  have hsymm : var k ∈ P (π.symm k) := by simpa [π] using hπ_mem (π.symm k)
  have hi_eq : i = π.symm k := by
    by_contra hne
    exact Finset.disjoint_left.mp (hd_ij i (π.symm k) hne) hk hsymm
  rw [hi_eq, Equiv.apply_symm_apply]

/-- Clauses (1) and (2) identify the `x`- and `y`-variables in each `zPartnerVars i F`:
`yVar k ∈ zPartnerVars i F ↔ k = i` and `xVar k ∈ zPartnerVars i F ↔ k = π i` for some
permutation `π` [ECCC TR20-183, Section 3, p. 26]. -/
private theorem ZDecomp.exists_perm_zPartnerVars {F : PosFormula (6 * n)} (hd : ZDecomp F)
    (heval_unit : ∀ x y : BitString (2 * n), ∀ i : Fin (2 * n),
      F.eval (packXYZ x y (Function.update zeros2n i true)) =
        decide (∃ v ∈ zPartnerVars i F,
          packXYZ x y (Function.update zeros2n i true) v = true))
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ i, y i = true ∧ z i = true))
    (hC2 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ ones2n y z) = decide (∃ i, z i = true)) :
    ∃ π : Equiv.Perm (Fin (2 * n)),
      (∀ i k, xVar k ∈ zPartnerVars i F ↔ k = π i) ∧
      (∀ i k, yVar k ∈ zPartnerVars i F ↔ k = i) := by
  have hy_mem (i : Fin (2 * n)) : yVar i ∈ zPartnerVars i F := by
    have h := hC1 (Function.update zeros2n i true) (Function.update zeros2n i true)
    rw [heval_unit, decide_eq_decide] at h
    obtain ⟨v, hv, hwv⟩ := h.mpr ⟨i, by simp, by simp⟩
    have hv_notZ : v ∉ zSet n := Finset.disjoint_left.mp (hd.disjoint_partner i) hv
    rcases eq_xVar_or_yVar_or_zVar v with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp at hwv
    · have hki : k = i := by
        by_contra hne
        simp [Function.update_of_ne hne] at hwv
      exact hki ▸ hv
    · exact absurd (zVar_mem_zSet k) hv_notZ
  have hx_exists (i : Fin (2 * n)) : ∃ k : Fin (2 * n), xVar k ∈ zPartnerVars i F := by
    have h := hC2 zeros2n (Function.update zeros2n i true)
    rw [heval_unit, decide_eq_decide] at h
    obtain ⟨v, hv, hwv⟩ := h.mpr ⟨i, by simp⟩
    have hv_notZ : v ∉ zSet n := Finset.disjoint_left.mp (hd.disjoint_partner i) hv
    rcases eq_xVar_or_yVar_or_zVar v with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k, hv⟩
    · simp at hwv
    · exact absurd (zVar_mem_zSet k) hv_notZ
  obtain ⟨π, hx_iff⟩ := exists_perm_and_mem_iff_of_disjoint hd.disjoint_ij hx_exists
  refine ⟨π, hx_iff, fun i k => ⟨fun hk => ?_, fun h => h ▸ hy_mem i⟩⟩
  by_contra hne
  exact Finset.disjoint_left.mp (hd.disjoint_ij k i hne) (hy_mem k) hk

/-- **Ilango's Lemma 12** [ECCC TR20-183, Section 3, Lemma 12, pp. 22, 24–26]: if
`F : PosFormula (6 * n)` is a read-once positive formula of leaf size $6n$ that agrees with
Clauses (1)–(4) of $\gamma_G$, then there exists a permutation $\pi \in S_{2n}$ such that for all
$x, y, z \in \{0, 1\}^{2n}$,
$$F.\mathrm{eval}(\mathrm{packXYZ}\, x\, y\, z) =
  \mathrm{decide}(\exists i \in \mathrm{Fin}\,(2n),\; (x(\pi(i)) \vee y(i)) \wedge z(i)).$$ -/
theorem _root_.Cslib.Circuits.Boolean.PosFormula.exists_perm_of_agreesWith_ilango
    {F : PosFormula (6 * n)} (hro : F.IsReadOnce) (hleaf : F.leafSize = 6 * n)
    (hC1 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ zeros2n y z) = decide (∃ i, y i = true ∧ z i = true))
    (hC2 : ∀ y z : BitString (2 * n),
      F.eval (packXYZ ones2n y z) = decide (∃ i, z i = true))
    (hC3 : ∀ x y : BitString (2 * n),
      F.eval (packXYZ x y ones2n) = decide (∃ i, x i = true ∨ y i = true))
    (hC4 : ∀ x y : BitString (2 * n),
      F.eval (packXYZ x y zeros2n) = false) :
    ∃ π : Equiv.Perm (Fin (2 * n)), ∀ x y z : BitString (2 * n),
      F.eval (packXYZ x y z) =
        decide (∃ i : Fin (2 * n), (x (π i) || y i) && z i) := by
  have hsupp : F.leafSupport = Finset.univ :=
    Finset.eq_univ_of_card F.leafSupport
      (by simpa using ((F.isReadOnce_iff_card_leafSupport_eq_leafSize).mp hro).trans hleaf)
  have hnotZF : NotZLeaf F := fun i hF => by
    have : F.leafSize = 1 := by rw [hF, PosFormula.leafSize_var]
    omega
  have hzF : zCount F = 2 * n := by simp [zCount, hsupp]
  have hand_le := (numAnd_le_two_mul_of_clause3 hro hleaf hC3).2
  have hz_le := zCount_le_numAnd_of_notZLeaf hro hC1 hC3 (.refl F) hnotZF
  have hd := structure_of_zCount_eq_numAnd hro hC1 hC3 (.refl F) hnotZF (by omega)
  obtain ⟨heval', heval_unit⟩ := hd.eval_packXYZ_of_clause4 hC4
  obtain ⟨π, hx_iff, hy_iff⟩ := hd.exists_perm_zPartnerVars heval_unit hC1 hC2
  refine ⟨π, fun x y z => ?_⟩
  rw [heval', decide_eq_decide]
  refine exists_congr fun i => ?_
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨hz, v, hv, hwv⟩
    refine ⟨?_, hz⟩
    have hv_notZ : v ∉ zSet n := Finset.disjoint_left.mp (hd.disjoint_partner i) hv
    rcases eq_xVar_or_yVar_or_zVar v with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [(hx_iff i k).mp hv] at hwv
      exact Or.inl (by simpa using hwv)
    · rw [(hy_iff i k).mp hv] at hwv
      exact Or.inr (by simpa using hwv)
    · exact absurd (zVar_mem_zSet k) hv_notZ
  · rintro ⟨hx | hy, hz⟩
    · exact ⟨hz, xVar (π i), (hx_iff i (π i)).mpr rfl, by simpa using hx⟩
    · exact ⟨hz, yVar i, (hy_iff i i).mpr rfl, by simpa using hy⟩

/-! ## Section 5: Ilango's Theorem 11 (Exact Equivalence for $n \ge 2$) -/

/-- The read-once positive formula $\bigvee_{i=1}^{2n} ((x_{\pi(i)} \vee y_i) \wedge z_i)$ of
gate size $6n - 1$ corresponding to a permutation $\pi \in S_{2n}$ [ECCC TR20-183, Section 3,
p. 22]. -/
@[expose] def ilangoPosFormula (hn : 0 < n) (π : Equiv.Perm (Fin (2 * n))) : PosFormula (6 * n) :=
  PosFormula.orFin (2 * n) (by omega) fun i =>
    .and (.or (.var (xVar (π i))) (.var (yVar i))) (.var (zVar i))

private theorem eval_ilangoPosFormula (hn : 0 < n) (π : Equiv.Perm (Fin (2 * n)))
    (x y z : BitString (2 * n)) :
    (ilangoPosFormula hn π).eval (packXYZ x y z) =
      decide (∃ i : Fin (2 * n), (x (π i) || y i) && z i) := by
  rw [ilangoPosFormula, PosFormula.eval_orFin]
  simp [PosFormula.eval]

private theorem leafSize_ilangoPosFormula (hn : 0 < n) (π : Equiv.Perm (Fin (2 * n))) :
    (ilangoPosFormula hn π).leafSize = 6 * n := by
  rw [ilangoPosFormula, PosFormula.leafSize_orFin_of_eq (2 * n) (by omega) _ 3 (fun _ => rfl)]
  omega

private theorem size_ilangoPosFormula (hn : 0 < n) (π : Equiv.Perm (Fin (2 * n))) :
    (ilangoPosFormula hn π).size = 6 * n - 1 := by
  have h1 := (ilangoPosFormula hn π).size_add_one
  have h2 := leafSize_ilangoPosFormula hn π
  omega

private theorem leafSupport_ilangoPosFormula (hn : 0 < n) (π : Equiv.Perm (Fin (2 * n))) :
    (ilangoPosFormula hn π).leafSupport = Finset.univ := by
  ext v
  simp only [Finset.mem_univ, iff_true, ilangoPosFormula, PosFormula.mem_leafSupport_orFin]
  rcases eq_xVar_or_yVar_or_zVar v with ⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨π.symm k, by simp [PosFormula.leafSupport]⟩
  · exact ⟨i, by simp [PosFormula.leafSupport]⟩
  · exact ⟨i, by simp [PosFormula.leafSupport]⟩

private theorem isReadOnce_ilangoPosFormula (hn : 0 < n) (π : Equiv.Perm (Fin (2 * n))) :
    (ilangoPosFormula hn π).IsReadOnce := by
  rw [PosFormula.isReadOnce_iff_card_leafSupport_eq_leafSize,
    leafSupport_ilangoPosFormula, leafSize_ilangoPosFormula]
  simp

/-- For any block-preserving permutation $\pi \in S_{2n}$ and indices
$j, j', k, k' \in \mathrm{Fin}\, n$, evaluating $\bigvee_i ((x_{\pi(i)} \vee y_i) \wedge z_i)$ on
$(\overline{e_k}\,\overline{e_{k'}}, 0^{2n}, e_j\,e_{j'})$ tests whether $\pi$ avoids mapping
both $j \mapsto k$ and $n + j' \mapsto n + k'$. -/
private theorem eval_antiUnitPair_unitPair_of_isBlockPreserving
    {π : Equiv.Perm (Fin (2 * n))} (hblock : BipartitePermutationGraph.IsBlockPreserving π)
    (j j' k k' : Fin n) :
    (∃ i : Fin (2 * n),
      ((antiUnitPair k k' (π i) || zeros2n i) && unitPair j j' i) = true) ↔
    ((π ⟨j.1, by omega⟩).1 = k.1 → (π ⟨n + j'.1, by omega⟩).1 ≠ n + k'.1) := by
  have hj_lt : (π ⟨j.1, by omega⟩).1 < n := (hblock ⟨j.1, by omega⟩).mp j.2
  have hj'_ge : ¬(π ⟨n + j'.1, by omega⟩).1 < n :=
    mt (hblock ⟨n + j'.1, by omega⟩).mpr (by simp)
  have h1 : antiUnitPair k k' (π ⟨j.1, by omega⟩) = true ↔ (π ⟨j.1, by omega⟩).1 ≠ k.1 := by
    simp only [antiUnitPair, Bool.not_eq_true', decide_eq_false_iff_not, not_or]
    exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  have h2 : antiUnitPair k k' (π ⟨n + j'.1, by omega⟩) = true ↔
      (π ⟨n + j'.1, by omega⟩).1 ≠ n + k'.1 := by
    simp only [antiUnitPair, Bool.not_eq_true', decide_eq_false_iff_not, not_or]
    have hk_lt := k.2
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  rw [imp_iff_not_or, ← ne_eq, ← h1, ← h2]
  constructor
  · rintro ⟨i, hi⟩
    simp only [zeros2n, Bool.or_false, Bool.and_eq_true, unitPair, decide_eq_true_eq] at hi
    rcases hi.2 with hij | hij'
    · exact Or.inl ((Fin.ext hij : i = ⟨j.1, by omega⟩) ▸ hi.1)
    · exact Or.inr ((Fin.ext hij' : i = ⟨n + j'.1, by omega⟩) ▸ hi.1)
  · rintro (h | h)
    · exact ⟨⟨j.1, by omega⟩, by simp [unitPair, h]⟩
    · exact ⟨⟨n + j'.1, by omega⟩, by simp [unitPair, h]⟩

/-- If $\pi \in S_{2n}$ satisfies `G.SatisfiesUndirected π`, then the read-once positive formula
`ilangoPosFormula hn π` agrees with `ilangoInstance G` on every defined entry
[ECCC TR20-183, Section 3, Theorem 11 (easy direction), pp. 23–24]. -/
theorem agreesWith_ilangoPosFormula_of_satisfiesUndirected {G : BipartitePermutationGraph}
    (hn : 0 < G.1) {π : Equiv.Perm (Fin (2 * G.1))} (hπ : G.SatisfiesUndirected π) :
    (ilangoInstance G).AgreesWith (ilangoPosFormula hn π).eval := by
  intro w b hwb
  change (ilangoInstance G).partialFunction w = some b at hwb
  rw [ilangoInstance_partialFunction] at hwb; rw [← packXYZ_unpack w] at hwb ⊢
  generalize unpackX w = x, unpackY w = y, unpackZ w = z at hwb ⊢
  rw [eval_ilangoPosFormula]
  unfold ilangoGamma at hwb
  simp only [unpackX_packXYZ, unpackY_packXYZ, unpackZ_packXYZ] at hwb
  split_ifs at hwb with hx0 hx1 hz1 hz0 hleft hright hedge
  · exact Option.some.inj hwb ▸ by simp [hx0]
  · exact Option.some.inj hwb ▸ by simp [hx1]
  · rw [← Option.some.inj hwb, hz1, decide_eq_decide]
    simp only [ones2n, Bool.and_true, Bool.or_eq_true, exists_or]
    exact or_congr_left ⟨fun ⟨i, hi⟩ => ⟨π i, hi⟩, fun ⟨j, hj⟩ => ⟨π.symm j, by simpa using hj⟩⟩
  · exact Option.some.inj hwb ▸ by simp [hz0]
  · rw [← Option.some.inj hwb, hleft.1, hleft.2, decide_eq_decide]
    simp only [zeros2n, leftHalfOnes, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨i, hx, hi⟩ => ⟨π i, (hπ.1 i).mp hi, hx⟩,
      fun ⟨j, hj, hx⟩ => ⟨π.symm j, by simpa using hx, (hπ.1.symm j).mp hj⟩⟩
  · rw [← Option.some.inj hwb, hright.1, hright.2, decide_eq_decide]
    simp only [zeros2n, rightHalfOnes, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨i, hx, hi⟩ => ⟨π i, not_lt.mp (mt (hπ.1 i).mpr (not_lt.mpr hi)), hx⟩,
      fun ⟨j, hj, hx⟩ =>
        ⟨π.symm j, by simpa using hx, not_lt.mp (mt (hπ.1.symm j).mpr (not_lt.mpr hj))⟩⟩
  · rw [decide_eq_true_iff] at hedge
    obtain ⟨j, j', k, k', he, rfl, rfl, rfl⟩ := hedge
    rw [← Option.some.inj hwb, decide_eq_true_iff,
      eval_antiUnitPair_unitPair_of_isBlockPreserving hπ.1]
    exact hπ.2 ((j.1, k.1), (j'.1, k'.1)) he j.2 k.2 j'.2 k'.2

/-- **Backward direction of Ilango's Theorem 11**: if $1 \le G.1$ and
`G ∈ BipartitePermutationIndependentSet`, then `ilangoInstance G ∈ PartialMCSP.MonotoneReadOnce`. -/
private theorem ilangoInstance_mem_monotoneReadOnce_of_mem {G : BipartitePermutationGraph}
    (hn : 0 < G.1) (hG : G ∈ BipartitePermutationIndependentSet) :
    ilangoInstance G ∈ PartialMCSP.MonotoneReadOnce := by
  obtain ⟨π, hπ⟩ :=
    (BipartitePermutationIndependentSet.mem_iff_exists_satisfiesUndirected G).mp hG
  change ∃ F : PosFormula (6 * G.1),
    F.IsReadOnce ∧ F.size ≤ 6 * G.1 - 1 ∧ (ilangoInstance G).AgreesWith F.eval
  exact ⟨ilangoPosFormula hn π, isReadOnce_ilangoPosFormula hn π,
    by rw [size_ilangoPosFormula],
    agreesWith_ilangoPosFormula_of_satisfiesUndirected hn hπ⟩

private theorem isBlockPreserving_of_agreesWith_leftHalfOnes {n : ℕ}
    {π : Equiv.Perm (Fin (2 * n))}
    (h : ∀ x : BitString (2 * n),
      decide (∃ i : Fin (2 * n), ((x (π i) || zeros2n i) && leftHalfOnes i) = true) =
        decide (∃ i : Fin (2 * n), i.1 < n ∧ x i = true)) :
    BipartitePermutationGraph.IsBlockPreserving π := by
  intro i
  have h1 := h (Function.update zeros2n (π i) true)
  rw [decide_eq_decide] at h1
  simp only [zeros2n, leftHalfOnes, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at h1
  have hLHS : (∃ j : Fin (2 * n),
      Function.update (zeros2n (n := n)) (π i) true (π j) = true ∧ j.1 < n) ↔ i.1 < n := by
    refine ⟨fun ⟨j, hj, hj_lt⟩ => ?_, fun hi_lt => ⟨i, by simp, hi_lt⟩⟩
    have hji : j = i := by
      by_contra hne
      simp [Function.update_of_ne (π.injective.ne hne)] at hj
    exact hji ▸ hj_lt
  have hRHS : (∃ j : Fin (2 * n),
      j.1 < n ∧ Function.update (zeros2n (n := n)) (π i) true j = true) ↔ (π i).1 < n := by
    refine ⟨fun ⟨j, hj_lt, hj⟩ => ?_, fun hπ_lt => ⟨π i, hπ_lt, by simp⟩⟩
    have hji : j = π i := by
      by_contra hne
      simp [Function.update_of_ne hne] at hj
    exact hji ▸ hj_lt
  exact (hLHS.symm.trans h1).trans hRHS

/-- **Forward direction of Ilango's Theorem 11** [ECCC TR20-183, Section 3, Theorem 11, pp. 21–24]:
if $2 \le G.1$ and `ilangoInstance G ∈ PartialMCSP.BinaryGate`, then
`G ∈ BipartitePermutationIndependentSet`. -/
private theorem mem_BipartitePermutationIndependentSet_of_ilangoInstance_mem_binaryGate
    {G : BipartitePermutationGraph} (hG : 2 ≤ G.1)
    (hmem : ilangoInstance G ∈ PartialMCSP.BinaryGate) :
    G ∈ BipartitePermutationIndependentSet := by
  obtain ⟨c, hc_cost, hc_agrees⟩ := hmem
  change (c : Circuit signature (6 * G.1) 1).program.cost binaryCost ≤ 6 * G.1 - 1 at hc_cost
  change (ilangoInstance G).AgreesWith
    (fun y => (c : Circuit signature (6 * G.1) 1).eval interpretation y 0) at hc_agrees
  have hpos (i : Fin (6 * G.1)) : ∃ y₀ y₁ : BitString (6 * G.1),
      (∀ k, k ≠ i → y₀ k = y₁ k) ∧ y₀ i = false ∧ y₁ i = true ∧
      c.eval interpretation y₀ 0 = false ∧ c.eval interpretation y₁ 0 = true := by
    obtain ⟨w, h0, h1⟩ := ilangoInstance_posEssential (by omega) hc_agrees i
    exact ⟨Function.update w i false, Function.update w i true,
      fun k hk => by simp [Function.update_of_ne hk], by simp, by simp, h0, h1⟩
  obtain ⟨F, hro, hleaf, _, _, hF_eval⟩ :=
    c.exists_posFormula_of_cost_binaryCost_le (show 0 < 6 * G.1 by omega)
      (show c.program.cost binaryCost + 1 ≤ 6 * G.1 by omega) hpos
  have hF_agrees (w : BitString (6 * G.1)) (b : Bool) (hwb : ilangoGamma G w = some b) :
      F.eval w = b := by
    rw [hF_eval]
    exact hc_agrees w b (by rwa [ilangoInstance_partialFunction])
  obtain ⟨π, hF_π⟩ := PosFormula.exists_perm_of_agreesWith_ilango hro hleaf
    (fun y z => hF_agrees _ _ (ilangoGamma_zeros2n_x G y z))
    (fun y z => hF_agrees _ _ (ilangoGamma_ones2n_x G y z))
    (fun x y => hF_agrees _ _ (ilangoGamma_ones2n_z G x y))
    (fun x y => hF_agrees _ _ (ilangoGamma_zeros2n_z G x y))
  rw [BipartitePermutationIndependentSet.mem_iff_exists_satisfiesUndirected]
  have hblock : BipartitePermutationGraph.IsBlockPreserving π :=
    isBlockPreserving_of_agreesWith_leftHalfOnes fun x => by
      rw [← hF_π]
      exact hF_agrees _ _ (ilangoGamma_leftHalfOnes G x)
  refine ⟨π, hblock, fun e he hu₁ hu₂ hv₁ hv₂ => ?_⟩
  have h7 := hF_agrees _ _
    (ilangoGamma_edge hG ⟨e.1.1, hu₁⟩ ⟨e.2.1, hv₁⟩ ⟨e.1.2, hu₂⟩ ⟨e.2.2, hv₂⟩ he)
  rwa [hF_π, decide_eq_true_iff, eval_antiUnitPair_unitPair_of_isBlockPreserving hblock] at h7

/-- **Ilango's Theorem 11 (monotone read-once equivalence for $n \ge 2$)**
[ECCC TR20-183, Section 3, Theorem 11, p. 20, proof pp. 21–24]: for $2 \le G.1$,
`G ∈ BipartitePermutationIndependentSet ↔ ilangoInstance G ∈ PartialMCSP.MonotoneReadOnce`. -/
theorem mem_BipartitePermutationIndependentSet_iff_ilangoInstance_mem_monotoneReadOnce
    {G : BipartitePermutationGraph} (hG : 2 ≤ G.1) :
    G ∈ BipartitePermutationIndependentSet ↔ ilangoInstance G ∈ PartialMCSP.MonotoneReadOnce :=
  ⟨ilangoInstance_mem_monotoneReadOnce_of_mem (by omega), fun h =>
    mem_BipartitePermutationIndependentSet_of_ilangoInstance_mem_binaryGate hG
      (monotoneReadOnce_subset_binaryGate h)⟩

/-- **Ilango's Theorem 11 (binary-gate equivalence for $n \ge 2$)**
[ECCC TR20-183, Section 3, Theorem 11, p. 20, proof pp. 21–24]: for $2 \le G.1$,
`G ∈ BipartitePermutationIndependentSet ↔ ilangoInstance G ∈ PartialMCSP.BinaryGate`. -/
theorem mem_BipartitePermutationIndependentSet_iff_ilangoInstance_mem_binaryGate
    {G : BipartitePermutationGraph} (hG : 2 ≤ G.1) :
    G ∈ BipartitePermutationIndependentSet ↔ ilangoInstance G ∈ PartialMCSP.BinaryGate :=
  ⟨fun h => monotoneReadOnce_subset_binaryGate
    (ilangoInstance_mem_monotoneReadOnce_of_mem (by omega) h),
    mem_BipartitePermutationIndependentSet_of_ilangoInstance_mem_binaryGate hG⟩

/-- **Ilango's Theorem 11 (all-gates equivalence for $n \ge 2$)**
[ECCC TR20-183, Section 3, Theorem 11, p. 20, proof pp. 21–24]: for $2 \le G.1$,
`G ∈ BipartitePermutationIndependentSet ↔ ilangoInstance G ∈ PartialMCSP`. -/
theorem mem_BipartitePermutationIndependentSet_iff_ilangoInstance_mem
    {G : BipartitePermutationGraph} (hG : 2 ≤ G.1) :
    G ∈ BipartitePermutationIndependentSet ↔ ilangoInstance G ∈ PartialMCSP :=
  ⟨fun h => monotoneReadOnce_subset
    (ilangoInstance_mem_monotoneReadOnce_of_mem (by omega) h),
    fun h => mem_BipartitePermutationIndependentSet_of_ilangoInstance_mem_binaryGate hG
      (mem_binaryGate_of_mem h)⟩

/-! ## Section 6: Total Reduction `ilangoReduction` and $2^{O(n)}$-Time Computability -/

/-- Trivial yes-instance of `PartialMCSP` on 1 variable with threshold 0 and all entries
undefined (`none`). -/
private def trivialYesInstance : Instance where
  arity := 1
  table _ := none
  threshold := 0

/-- Trivial no-instance of `PartialMCSP` on 2 variables with threshold 0 and truth table for
$x_0 \wedge x_1$. -/
private def trivialNoInstance : Instance where
  arity := 2
  table i := some (i.1 == 3)
  threshold := 0

private theorem trivialYesInstance_mem_monotoneReadOnce :
    trivialYesInstance ∈ PartialMCSP.MonotoneReadOnce :=
  ⟨.var ⟨0, Nat.zero_lt_one⟩, trivial, le_rfl, fun _ _ h => by cases h⟩

private theorem trivialYesInstance_mem_binaryGate :
    trivialYesInstance ∈ PartialMCSP.BinaryGate :=
  monotoneReadOnce_subset_binaryGate trivialYesInstance_mem_monotoneReadOnce

private theorem trivialYesInstance_mem :
    trivialYesInstance ∈ PartialMCSP :=
  monotoneReadOnce_subset trivialYesInstance_mem_monotoneReadOnce

private theorem trivialNoInstance_essentialAt :
    ∀ j : Fin trivialNoInstance.arity, trivialNoInstance.EssentialAt j := by
  intro j
  fin_cases j
  · refine ⟨fun i => decide (i.1 = 1), fun _ => true, false, true, ?_, by decide, by decide,
      by decide⟩
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · rfl
  · refine ⟨fun i => decide (i.1 = 0), fun _ => true, false, true, ?_, by decide, by decide,
      by decide⟩
    intro k hk
    fin_cases k
    · rfl
    · exact absurd rfl hk

private theorem trivialNoInstance_not_mem_binaryGate :
    trivialNoInstance ∉ PartialMCSP.BinaryGate :=
  not_mem_binaryGate_of_threshold_lt trivialNoInstance_essentialAt (by decide)

private theorem trivialNoInstance_not_mem :
    trivialNoInstance ∉ PartialMCSP :=
  fun h => trivialNoInstance_not_mem_binaryGate (mem_binaryGate_of_mem h)

private theorem trivialNoInstance_not_mem_monotoneReadOnce :
    trivialNoInstance ∉ PartialMCSP.MonotoneReadOnce :=
  fun h => trivialNoInstance_not_mem (monotoneReadOnce_subset h)

/-- Direct decision procedure for `BipartitePermutationIndependentSet` when $G.1 < 2$. -/
private def decideSmallBPIS (G : BipartitePermutationGraph) : Bool :=
  if G.1 == 0 then true
  else !(G.2.any fun e => e.1.1 == 0 && e.1.2 == 0 && e.2.1 == 0 && e.2.2 == 0)

private theorem decideSmallBPIS_eq_true_iff {G : BipartitePermutationGraph} (hG : G.1 < 2) :
    decideSmallBPIS G = true ↔ G ∈ BipartitePermutationIndependentSet := by
  rcases G with ⟨n, E⟩
  dsimp at hG
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · simp only [decideSmallBPIS, beq_self_eq_true, ↓reduceIte, true_iff]
    exact ⟨1, 1, fun e _ hu₁ => absurd hu₁ (Nat.not_lt_zero _)⟩
  · simp only [decideSmallBPIS, show (1 == 0) = false by rfl, Bool.false_eq_true, ↓reduceIte,
      Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, beq_iff_eq]
    refine ⟨fun h => ⟨1, 1, fun e he hu₁ hu₂ hv₁ hv₂ _ _ =>
      absurd ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩ (h e he)⟩, ?_⟩
    rintro ⟨π₁, π₂, hSat⟩ e he ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact hSat e he (by omega) (by omega) (by omega) (by omega)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- **Total reduction from `BipartitePermutationIndependentSet` to `PartialMCSP`**
[Ilango2020FOCS, Section III.B, p. 428; ECCC TR20-183, Section 3, Theorem 11, pp. 20–21]: maps $G$
to `ilangoInstance G` when $2 \le G.1$, and to `trivialYesInstance` / `trivialNoInstance` when
$G.1 < 2$. -/
def ilangoReduction (G : BipartitePermutationGraph) : Instance :=
  if G.1 < 2 then
    if decideSmallBPIS G then trivialYesInstance else trivialNoInstance
  else
    ilangoInstance G

theorem mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem_monotoneReadOnce
    (G : BipartitePermutationGraph) :
    G ∈ BipartitePermutationIndependentSet ↔
      ilangoReduction G ∈ PartialMCSP.MonotoneReadOnce := by
  unfold ilangoReduction
  split_ifs with hG hsmall
  · simp [(decideSmallBPIS_eq_true_iff hG).mp hsmall, trivialYesInstance_mem_monotoneReadOnce]
  · have hnot : G ∉ BipartitePermutationIndependentSet :=
      mt (decideSmallBPIS_eq_true_iff hG).mpr hsmall
    simp [hnot, trivialNoInstance_not_mem_monotoneReadOnce]
  · exact mem_BipartitePermutationIndependentSet_iff_ilangoInstance_mem_monotoneReadOnce (by omega)

theorem mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem_binaryGate
    (G : BipartitePermutationGraph) :
    G ∈ BipartitePermutationIndependentSet ↔
      ilangoReduction G ∈ PartialMCSP.BinaryGate := by
  unfold ilangoReduction
  split_ifs with hG hsmall
  · simp [(decideSmallBPIS_eq_true_iff hG).mp hsmall, trivialYesInstance_mem_binaryGate]
  · have hnot : G ∉ BipartitePermutationIndependentSet :=
      mt (decideSmallBPIS_eq_true_iff hG).mpr hsmall
    simp [hnot, trivialNoInstance_not_mem_binaryGate]
  · exact mem_BipartitePermutationIndependentSet_iff_ilangoInstance_mem_binaryGate (by omega)

theorem mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem
    (G : BipartitePermutationGraph) :
    G ∈ BipartitePermutationIndependentSet ↔ ilangoReduction G ∈ PartialMCSP := by
  unfold ilangoReduction
  split_ifs with hG hsmall
  · simp [(decideSmallBPIS_eq_true_iff hG).mp hsmall, trivialYesInstance_mem]
  · have hnot : G ∉ BipartitePermutationIndependentSet :=
      mt (decideSmallBPIS_eq_true_iff hG).mpr hsmall
    simp [hnot, trivialNoInstance_not_mem]
  · exact mem_BipartitePermutationIndependentSet_iff_ilangoInstance_mem (by omega)

/-! ### Bitwise list evaluator and $2^{O(n)}$-time computability of `ilangoReduction` -/

/-- Bitwise list evaluator for the $m$-th truth-table entry of `ilangoInstance G`. -/
private def ilangoEntry (G : BipartitePermutationGraph) (m : ℕ) : Option Bool :=
  let n := G.1
  let idx := List.range (2 * n)
  if idx.all fun i => !m.testBit i then
    some (idx.any fun i => m.testBit (2 * n + i) && m.testBit (4 * n + i))
  else if idx.all fun i => m.testBit i then
    some (idx.any fun i => m.testBit (4 * n + i))
  else if idx.all fun i => m.testBit (4 * n + i) then
    some (idx.any fun i => m.testBit i || m.testBit (2 * n + i))
  else if idx.all fun i => !m.testBit (4 * n + i) then
    some false
  else if (idx.all fun i => m.testBit (4 * n + i) == decide (i < n)) &&
      (idx.all fun i => !m.testBit (2 * n + i)) then
    some (idx.any fun i => decide (i < n) && m.testBit i)
  else if (idx.all fun i => m.testBit (4 * n + i) == decide (n ≤ i)) &&
      (idx.all fun i => !m.testBit (2 * n + i)) then
    some (idx.any fun i => decide (n ≤ i) && m.testBit i)
  else if G.2.any fun e =>
      decide (e.1.1 < n) && decide (e.1.2 < n) && decide (e.2.1 < n) && decide (e.2.2 < n) &&
      (idx.all fun i => m.testBit i == !(i == e.1.2 || i == n + e.2.2)) &&
      (idx.all fun i => !m.testBit (2 * n + i)) &&
      (idx.all fun i => m.testBit (4 * n + i) == (i == e.1.1 || i == n + e.2.1)) then
    some true
  else
    none

private theorem range_all_eq_decide {m : ℕ} (f : ℕ → Bool) (b g : Fin m → Bool)
    (hf : ∀ i : Fin m, f i.1 = (b i == g i)) :
    (List.range m).all f = decide (b = g) := by
  rw [← Bool.decide_coe ((List.range m).all f), decide_eq_decide, List.all_eq_true]
  simp only [List.mem_range, funext_iff, Fin.forall_iff]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [hf ⟨i, hi⟩, beq_iff_eq]

private theorem range_any_eq_decide {m : ℕ} (f : ℕ → Bool) (p : Fin m → Prop) [DecidablePred p]
    (hf : ∀ i : Fin m, f i.1 = decide (p i)) :
    (List.range m).any f = decide (∃ i : Fin m, p i) := by
  rw [← Bool.decide_coe ((List.range m).any f), decide_eq_decide, List.any_eq_true]
  simp only [List.mem_range]
  exact ⟨fun ⟨i, hi, hfi⟩ => ⟨⟨i, hi⟩, by rwa [hf ⟨i, hi⟩, decide_eq_true_iff] at hfi⟩,
    fun ⟨⟨i, hi⟩, hpi⟩ => ⟨i, hi, by rw [hf ⟨i, hi⟩, decide_eq_true_iff]; exact hpi⟩⟩

private theorem ilangoEntry_edge_eq_decide (G : BipartitePermutationGraph) (m : ℕ)
    (x y z : BitString (2 * G.1))
    (hx : ∀ i : Fin (2 * G.1), m.testBit i.1 = x i)
    (hy : ∀ i : Fin (2 * G.1), m.testBit (2 * G.1 + i.1) = y i)
    (hz : ∀ i : Fin (2 * G.1), m.testBit (4 * G.1 + i.1) = z i) :
    (G.2.any fun e =>
      decide (e.1.1 < G.1) && decide (e.1.2 < G.1) &&
      decide (e.2.1 < G.1) && decide (e.2.2 < G.1) &&
      ((List.range (2 * G.1)).all fun i =>
        m.testBit i == !(i == e.1.2 || i == G.1 + e.2.2)) &&
      ((List.range (2 * G.1)).all fun i => !m.testBit (2 * G.1 + i)) &&
      ((List.range (2 * G.1)).all fun i =>
        m.testBit (4 * G.1 + i) == (i == e.1.1 || i == G.1 + e.2.1))) =
      decide (∃ j j' k₀ k₀' : Fin G.1,
        ((j.1, k₀.1), (j'.1, k₀'.1)) ∈ G.2 ∧
        x = antiUnitPair k₀ k₀' ∧ y = zeros2n ∧ z = unitPair j j') := by
  have hcondy0 : ((List.range (2 * G.1)).all fun i => !m.testBit (2 * G.1 + i)) =
      decide (y = zeros2n) :=
    range_all_eq_decide _ y zeros2n fun i => by simp [hy i, zeros2n]
  rw [← Bool.decide_coe (G.2.any _), decide_eq_decide, List.any_eq_true]
  constructor
  · rintro ⟨e, he, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hj, hk₀⟩, hj'⟩, hk₀'⟩, hx_eq⟩, hy_eq⟩, hz_eq⟩ := h
    let j : Fin G.1 := ⟨e.1.1, hj⟩
    let k₀ : Fin G.1 := ⟨e.1.2, hk₀⟩
    let j' : Fin G.1 := ⟨e.2.1, hj'⟩
    let k₀' : Fin G.1 := ⟨e.2.2, hk₀'⟩
    rw [range_all_eq_decide _ x (antiUnitPair k₀ k₀') (fun i => by
      simp [hx i, antiUnitPair, k₀, k₀', Bool.decide_or, beq_eq_decide]),
      decide_eq_true_iff] at hx_eq
    rw [hcondy0, decide_eq_true_iff] at hy_eq
    rw [range_all_eq_decide _ z (unitPair j j') (fun i => by
      simp [hz i, unitPair, j, j', Bool.decide_or, beq_eq_decide]),
      decide_eq_true_iff] at hz_eq
    exact ⟨j, j', k₀, k₀', he, hx_eq, hy_eq, hz_eq⟩
  · rintro ⟨j, j', k₀, k₀', he, hx_eq, hy_eq, hz_eq⟩
    refine ⟨((j.1, k₀.1), (j'.1, k₀'.1)), he, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, j.2, k₀.2, j'.2, k₀'.2, true_and]
    refine ⟨⟨?_, by rw [hcondy0, hy_eq]; exact decide_eq_true rfl⟩, ?_⟩
    · rw [range_all_eq_decide _ x (antiUnitPair k₀ k₀') (fun i => by
        simp [hx i, antiUnitPair, Bool.decide_or, beq_eq_decide]), hx_eq]
      exact decide_eq_true rfl
    · rw [range_all_eq_decide _ z (unitPair j j') (fun i => by
        simp [hz i, unitPair, Bool.decide_or, beq_eq_decide]), hz_eq]
      exact decide_eq_true rfl

private theorem ilangoEntry_eq_table (G : BipartitePermutationGraph) (k : Fin (2 ^ (6 * G.1))) :
    ilangoEntry G k.1 = (ilangoInstance G).table k := by
  set w := (BitString.equivFin (6 * G.1)).symm k
  set x := unpackX w; set y := unpackY w; set z := unpackZ w
  have hx (i : Fin (2 * G.1)) : k.1.testBit i.1 = x i := by simp [x, w, unpackX, xVar]
  have hy (i : Fin (2 * G.1)) : k.1.testBit (2 * G.1 + i.1) = y i := by simp [y, w, unpackY, yVar]
  have hz (i : Fin (2 * G.1)) : k.1.testBit (4 * G.1 + i.1) = z i := by simp [z, w, unpackZ, zVar]
  have hcond1 := range_all_eq_decide (fun i => !k.1.testBit i) x zeros2n fun i => by
    simp [hx i, zeros2n]
  have hcond2 := range_all_eq_decide (fun i => k.1.testBit i) x ones2n fun i => by
    simp [hx i, ones2n]
  have hcond3 := range_all_eq_decide (fun i => k.1.testBit (4 * G.1 + i)) z ones2n fun i => by
    simp [hz i, ones2n]
  have hcond4 := range_all_eq_decide (fun i => !k.1.testBit (4 * G.1 + i)) z zeros2n fun i => by
    simp [hz i, zeros2n]
  have hcondy0 := range_all_eq_decide (fun i => !k.1.testBit (2 * G.1 + i)) y zeros2n fun i => by
    simp [hy i, zeros2n]
  have hcondzL := range_all_eq_decide (fun i => k.1.testBit (4 * G.1 + i) == decide (i < G.1))
    z leftHalfOnes fun i => by simp [hz i, leftHalfOnes]
  have hcondzR := range_all_eq_decide (fun i => k.1.testBit (4 * G.1 + i) == decide (G.1 ≤ i))
    z rightHalfOnes fun i => by simp [hz i, rightHalfOnes]
  have hval1 := range_any_eq_decide
    (fun i => k.1.testBit (2 * G.1 + i) && k.1.testBit (4 * G.1 + i))
    (fun i => y i = true ∧ z i = true) fun i => by simp [hy i, hz i, Bool.decide_and]
  have hval2 := range_any_eq_decide (fun i => k.1.testBit (4 * G.1 + i))
    (fun i => z i = true) fun i => by simp [hz i]
  have hval3 := range_any_eq_decide (fun i => k.1.testBit i || k.1.testBit (2 * G.1 + i))
    (fun i => x i = true ∨ y i = true) fun i => by simp [hx i, hy i, Bool.decide_or]
  have hval5 := range_any_eq_decide (fun i => decide (i < G.1) && k.1.testBit i)
    (fun i => i.1 < G.1 ∧ x i = true) fun i => by simp [hx i, Bool.decide_and]
  have hval6 := range_any_eq_decide (fun i => decide (G.1 ≤ i) && k.1.testBit i)
    (fun i => G.1 ≤ i.1 ∧ x i = true) fun i => by simp [hx i, Bool.decide_and]
  dsimp [ilangoEntry, ilangoInstance, ilangoGamma]
  change (if ((List.range (2 * G.1)).all fun i => !k.1.testBit i) = true then _ else _) =
    if x = zeros2n then _ else _
  rw [ilangoEntry_edge_eq_decide G k.1 x y z hx hy hz, hcond1, hcond2, hcond3, hcond4, hcondzL,
    hcondzR, hcondy0, hval1, hval2, hval3, hval5, hval6]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rfl

private theorem ofFn_ilangoInstance_table (G : BipartitePermutationGraph) :
    List.ofFn (ilangoInstance G).table =
      (List.range (2 ^ (6 * G.1))).map (ilangoEntry G) := by
  apply List.ext_getElem
  · simp [ilangoInstance]
  · intro i hi₁ hi₂
    rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact (ilangoEntry_eq_table G ⟨i, by simpa [ilangoInstance] using hi₁⟩).symm

/-- Raw pair representation `(List.ofFn (ilangoReduction G).table, (ilangoReduction G).threshold)`
computed from `(G, 2 ^ (6 * G.1))`. -/
private def ilangoRawFromFuel (p : BipartitePermutationGraph × ℕ) : List (Option Bool) × ℕ :=
  if decide (p.1.1 < 2) then
    if decideSmallBPIS p.1 then
      ([none, none], 0)
    else
      ([some false, some false, some false, some true], 0)
  else
    ((List.range p.2).map (ilangoEntry p.1), 6 * p.1.1 - 1)

private theorem ilangoRawFromFuel_eq (G : BipartitePermutationGraph) :
    ilangoRawFromFuel (G, 2 ^ (6 * G.1)) =
      (List.ofFn (ilangoReduction G).table, (ilangoReduction G).threshold) := by
  change ilangoRawFromFuel (G, 2 ^ (6 * G.1)) =
    (fun I : Instance => (List.ofFn I.table, I.threshold)) (ilangoReduction G)
  unfold ilangoRawFromFuel
  dsimp only
  by_cases hG : G.1 < 2
  · by_cases hsmall : decideSmallBPIS G
    · have hred : ilangoReduction G = trivialYesInstance := by simp [ilangoReduction, hG, hsmall]
      rw [hred]; simp [hG, hsmall, trivialYesInstance]
    · have hred : ilangoReduction G = trivialNoInstance := by simp [ilangoReduction, hG, hsmall]
      rw [hred]; simp [hG, hsmall, trivialNoInstance]
  · have hred : ilangoReduction G = ilangoInstance G := by simp [ilangoReduction, hG]
    rw [hred]
    simp only [hG, decide_false, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    exact ⟨(ofFn_ilangoInstance_table G).symm, rfl⟩

attribute [local fun_prop] ComputableInPolyTime.unary_range'

open ComputableInPolyTime in
@[local fun_prop] private theorem computableInPolyTime_decideSmallBPIS :
    ComputableInPolyTime decideSmallBPIS encBipartitePermutationGraph encBool := by
  unfold decideSmallBPIS BipartitePermutationGraph encBipartitePermutationGraph
  refine ite' (encC := encBool) (by fun_prop) (by fun_prop) (by fun_prop)

open ComputableInPolyTime in
@[local fun_prop] private theorem computableInPolyTime_ilangoEntry :
    ComputableInPolyTime (fun p : BipartitePermutationGraph × ℕ => ilangoEntry p.1 p.2)
      (encPair encBipartitePermutationGraph encUnary) (encOption encBool) := by
  unfold ilangoEntry BipartitePermutationGraph encBipartitePermutationGraph
  simp only [List.all_eq_not_any_not]
  refine ite' (encC := encBool) (by fun_prop) (by fun_prop) ?_
  refine ite' (encC := encBool) (by fun_prop) (by fun_prop) ?_
  refine ite' (encC := encBool) (by fun_prop) (by fun_prop) ?_
  refine ite' (encC := encBool) (by fun_prop) (by fun_prop) ?_
  refine ite' (encC := encBool) (by fun_prop) (by fun_prop) ?_
  refine ite' (encC := encBool) (by fun_prop) (by fun_prop) ?_
  refine ite' (encC := encBool) (by fun_prop) (by fun_prop) (by fun_prop)

open ComputableInPolyTime in
private theorem computableInPolyTime_ilangoRawFromFuel :
    ComputableInPolyTime ilangoRawFromFuel
      (encPair encBipartitePermutationGraph encUnary)
      (encPair (encList (encOption encBool)) encUnary) := by
  have h1 := computableInPolyTime_decideSmallBPIS
  have h2 := computableInPolyTime_ilangoEntry
  unfold ilangoRawFromFuel BipartitePermutationGraph encBipartitePermutationGraph at *
  refine ite' (by fun_prop)
    (ite' (by fun_prop) (by fun_prop) (by fun_prop)) ?_
  fun_prop

private theorem foldl_double_replicate (k : ℕ) (acc : ℕ) :
    (List.replicate k true).foldl (fun n _ => n + n) acc = acc * 2 ^ k := by
  induction k generalizing acc with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    ring

private theorem computableInO_twoPow :
    ComputableInO (fun m : ℕ => 2 ^ m) encUnary encUnary
      (fun m => 2 ^ (2 * m)) (fun m => 2 ^ (2 * m)) := by
  have hlist : ComputableInO (fun m : ℕ => List.replicate m true) encUnary encBits
      (fun m => (encUnary m).length) (fun m => (encUnary m).length) :=
    ComputableInO.of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl
  have hstep : ComputableInO (fun p : ℕ × Bool => p.1 + p.1)
      (encPair encUnary encBool) encUnary
      (fun p => (encPair encUnary encBool p).length + (encPair encUnary encBool p).length)
      (fun p => (encPair encUnary encBool p).length + (encPair encUnary encBool p).length) :=
    (ComputableInO.fst encUnary encBool).append
      (ComputableInO.fst encUnary encBool)
      (fun _ => by simp only [encUnary_apply, List.replicate_add])
  have hstep_bound (m i : ℕ) (_ : i < (List.replicate m true).length) :
      (let p := (((List.replicate m true).take i).foldl (fun n _ => n + n) 1,
        (List.replicate m true)[i]);
      (encPair encUnary encBool p).length + (encPair encUnary encBool p).length) ≤
        4 * 2 ^ m + 4 := by
    have := Nat.pow_le_pow_right two_pos (Nat.min_le_right i m)
    rw [List.take_replicate, foldl_double_replicate, one_mul]
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBool_apply,
      List.length_singleton]
    omega
  have hfold := ComputableInO.foldl (encA := encBool) (encL := encBits) (encB := encUnary)
    (step := fun n _ => n + n) hlist (ComputableInO.const 1) hstep
    (R := fun m => 4 * 2 ^ m + 4) (Q := fun m => 4 * 2 ^ m + 4) (B := fun m => 2 ^ m)
    hstep_bound hstep_bound (fun m i _ => by
      have := Nat.pow_le_pow_right two_pos (Nat.min_le_right i m)
      rw [List.take_replicate, foldl_double_replicate, one_mul, encUnary_apply,
        List.length_replicate]
      omega)
  refine (hfold.mono 16 (fun m => ?_) (fun m => ?_)).of_enc_eq fun m => ?_
  · simp only [encUnary_apply, encBits_apply, List.length_replicate]
    have hm : m < 2 ^ m := Nat.lt_two_pow_self
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [show 2 ^ (2 * m) = 2 ^ m * 2 ^ m by rw [← pow_add, two_mul]]
    generalize 2 ^ m = X at hm h1 ⊢; nlinarith
  · simp only [encUnary_apply, encBits_apply, List.length_replicate]
    have hm : m < 2 ^ m := Nat.lt_two_pow_self
    have hle : 2 ^ m ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right two_pos (by omega)
    omega
  · simp [foldl_double_replicate]

private theorem computableInPolyTime_sixMulFst :
    ComputableInPolyTime (fun G : BipartitePermutationGraph => 6 * G.1)
      encBipartitePermutationGraph encUnary := by
  unfold BipartitePermutationGraph encBipartitePermutationGraph
  fun_prop

private theorem ilangoReduction_time_bound (d₁ d₂ : ℕ) (G : BipartitePermutationGraph) :
    (encBipartitePermutationGraph G).length +
      (((encBipartitePermutationGraph G).length + 1) ^ d₁ + 2 ^ (2 * (6 * G.1))) +
      ((encPair encBipartitePermutationGraph encUnary (G, 2 ^ (6 * G.1))).length + 1) ^ d₂ ≤
      (3 ^ d₂ + 3) *
        (2 ^ ((12 + 6 * d₂) * G.1) *
          ((encBipartitePermutationGraph G).length + 1) ^ (d₁ + d₂ + 1) + 1) := by
  set C : ℕ := 12 + 6 * d₂
  set D : ℕ := d₁ + d₂ + 1
  set L := (encBipartitePermutationGraph G).length
  set M := 2 ^ (6 * G.1)
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hL1 : 1 ≤ L + 1 := Nat.succ_pos L
  have hX1 : 1 ≤ 2 ^ (C * G.1) := Nat.one_le_two_pow
  have hP1 : 1 ≤ (L + 1) ^ D := Nat.one_le_pow _ _ hL1
  have hL_le : L ≤ (L + 1) ^ D :=
    (Nat.le_succ L).trans (Nat.le_self_pow (by omega : D ≠ 0) (L + 1))
  have hd₁_le : (L + 1) ^ d₁ ≤ (L + 1) ^ D := Nat.pow_le_pow_right hL1 (by omega)
  have hd₂_le : (L + 1) ^ d₂ ≤ (L + 1) ^ D := Nat.pow_le_pow_right hL1 (by omega)
  have h12_le : 2 ^ (2 * (6 * G.1)) ≤ 2 ^ (C * G.1) :=
    Nat.pow_le_pow_right two_pos (by simp only [C]; nlinarith)
  have hpair_len : (encPair encBipartitePermutationGraph encUnary (G, M)).length + 1 ≤
      3 * M * (L + 1) := by
    simp only [length_encPair, encUnary_apply, List.length_replicate, L]; nlinarith
  have hpow_pair : ((encPair encBipartitePermutationGraph encUnary (G, M)).length + 1) ^ d₂ ≤
      3 ^ d₂ * (2 ^ (C * G.1) * (L + 1) ^ D) := by
    have hMd₂ : M ^ d₂ ≤ 2 ^ (C * G.1) := by
      rw [show M ^ d₂ = 2 ^ (6 * G.1 * d₂) by simp [M, ← pow_mul]]
      exact Nat.pow_le_pow_right two_pos (by simp only [C]; nlinarith)
    calc ((encPair encBipartitePermutationGraph encUnary (G, M)).length + 1) ^ d₂
        ≤ (3 * M * (L + 1)) ^ d₂ := Nat.pow_le_pow_left hpair_len d₂
      _ = 3 ^ d₂ * (M ^ d₂ * (L + 1) ^ d₂) := by simp only [mul_pow, mul_assoc]
      _ ≤ 3 ^ d₂ * (2 ^ (C * G.1) * (L + 1) ^ D) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hMd₂ hd₂_le)
  have ht1 : L ≤ 2 ^ (C * G.1) * (L + 1) ^ D := hL_le.trans (Nat.le_mul_of_pos_left _ hX1)
  have ht2 : (L + 1) ^ d₁ ≤ 2 ^ (C * G.1) * (L + 1) ^ D :=
    hd₁_le.trans (Nat.le_mul_of_pos_left _ hX1)
  have ht3 : 2 ^ (2 * (6 * G.1)) ≤ 2 ^ (C * G.1) * (L + 1) ^ D :=
    h12_le.trans (Nat.le_mul_of_pos_right _ hP1)
  generalize 2 ^ (C * G.1) * (L + 1) ^ D = W at ht1 ht2 ht3 hpow_pair ⊢
  generalize 3 ^ d₂ = K₃ at hpow_pair ⊢
  nlinarith

/-- **Plain $2^{O(n)}$-time computability of Ilango's reduction** under unary threshold encoding
(`PartialMCSP.enc`) [Ilango2020FOCS, Section III.B, p. 428; ECCC TR20-183, Section 3, Theorem 11,
pp. 20–21]. -/
theorem exists_computableInO_ilangoReduction :
    ∃ C D : ℕ, ComputableInO ilangoReduction
      encBipartitePermutationGraph PartialMCSP.enc
      (fun G => 2 ^ (C * G.1) * ((encBipartitePermutationGraph G).length + 1) ^ D)
      (fun G => 2 ^ (C * G.1) * ((encBipartitePermutationGraph G).length + 1) ^ D) := by
  obtain ⟨d₁, _, hd₁⟩ := computableInPolyTime_sixMulFst.exists_degree
  obtain ⟨d₂, _, hd₂⟩ := computableInPolyTime_ilangoRawFromFuel.exists_degree
  have hId : ComputableInO (fun G : BipartitePermutationGraph => G)
      encBipartitePermutationGraph encBipartitePermutationGraph
      (fun G => (encBipartitePermutationGraph G).length)
      (fun G => (encBipartitePermutationGraph G).length) :=
    ComputableInO.of_eq (encIn := encBipartitePermutationGraph)
      (encMid := encBipartitePermutationGraph) fun _ => rfl
  have hFuel : ComputableInO (fun G : BipartitePermutationGraph => 2 ^ (6 * G.1))
      encBipartitePermutationGraph encUnary
      (fun G => ((encBipartitePermutationGraph G).length + 1) ^ d₁ + 2 ^ (2 * (6 * G.1)))
      (fun G => ((encBipartitePermutationGraph G).length + 1) ^ d₁ + 2 ^ (2 * (6 * G.1))) :=
    computableInO_twoPow.comp hd₁.inO
  have hComp := hd₂.inO.comp (hId.prod hFuel)
  refine ⟨12 + 6 * d₂, d₁ + d₂ + 1, (hComp.mono (3 ^ d₂ + 3)
    (ilangoReduction_time_bound d₁ d₂) (ilangoReduction_time_bound d₁ d₂)).of_enc_eq fun G => ?_⟩
  rw [enc_apply, ← ilangoRawFromFuel_eq]
  rfl

/-! ## Section 7: Subexponential-Time Transfer and Ilango's ETH Lower Bounds -/

/-- The truth-table size $N = 2^m$ of a `PartialMCSP.Instance` of arity $m$
[Ilango2020FOCS, Theorem I.3, p. 424; ECCC TR20-183, Section 1.2.2, Theorem 3, p. 6]. -/
@[expose] def Instance.tableSize (x : Instance) : ℕ :=
  2 ^ x.arity

@[simp] theorem Instance.log_tableSize (x : Instance) :
    Nat.log 2 x.tableSize = x.arity :=
  Nat.log_pow Nat.one_lt_two x.arity

/-- The arity measure $m \log_2 m$ on `ilangoReduction G` is at most $24 n \log_2 n + 2$. -/
private theorem arity_mul_log_ilangoReduction_le (G : BipartitePermutationGraph) :
    (ilangoReduction G).arity * Nat.log 2 (ilangoReduction G).arity ≤
      24 * (G.1 * Nat.log 2 G.1) + 2 := by
  unfold ilangoReduction
  split_ifs with hG hsmall
  · simp [trivialYesInstance]
  · have : (trivialNoInstance).arity * Nat.log 2 (trivialNoInstance).arity = 2 := by decide
    rw [this]; omega
  · simp only [ilangoInstance]
    have hG2 : 2 ≤ G.1 := by omega
    have hlog8 : Nat.log 2 (6 * G.1) ≤ Nat.log 2 (8 * G.1) := Nat.log_mono_right (by omega)
    have h8 : 8 * G.1 = G.1 * 2 * 2 * 2 := by ring
    have hlog_eq : Nat.log 2 (8 * G.1) = Nat.log 2 G.1 + 3 := by
      rw [h8, Nat.log_mul_base Nat.one_lt_two (by omega),
        Nat.log_mul_base Nat.one_lt_two (by omega),
        Nat.log_mul_base Nat.one_lt_two (by omega)]
    have hlog1 : 1 ≤ Nat.log 2 G.1 := Nat.log_pos Nat.one_lt_two (by omega)
    have hlog_le : Nat.log 2 (6 * G.1) ≤ 4 * Nat.log 2 G.1 := by omega
    calc 6 * G.1 * Nat.log 2 (6 * G.1)
        ≤ 6 * G.1 * (4 * Nat.log 2 G.1) := Nat.mul_le_mul_left _ hlog_le
      _ ≤ 24 * (G.1 * Nat.log 2 G.1) + 2 := by ring_nf; omega

/-- **Subexponential-time transfer along Ilango's $2^{O(n)}$-time reduction** (unary threshold
encoding `PartialMCSP.enc`): if a target problem `B` on `PartialMCSP.Instance` is decidable in time
$2^{o(m \log m)}$ and `ilangoReduction` reduces `BipartitePermutationIndependentSet` to `B`, then
`BipartitePermutationIndependentSet` is decidable in time $2^{o(n \log n)}$. -/
private theorem decidableInSubexpTime_bpis_of_ilangoReduction
    {B : Set Instance}
    (hiff : ∀ G, G ∈ BipartitePermutationIndependentSet ↔ ilangoReduction G ∈ B)
    (hsub : DecidableInSubexpTime B PartialMCSP.enc fun I => I.arity * Nat.log 2 I.arity) :
    DecidableInSubexpTime BipartitePermutationIndependentSet encBipartitePermutationGraph
      fun G => G.1 * Nat.log 2 G.1 :=
  hsub.of_expReduction exists_computableInO_ilangoReduction hiff
    (c := 24) fun G => (arity_mul_log_ilangoReduction_le G).trans (by omega)

/-- Any subexponential-time decider for a problem `B` on `PartialMCSP.Instance` under binary
threshold encoding (`PartialMCSP.encBinary`) yields one under unary threshold encoding
(`PartialMCSP.enc`) via `computableInPolyTime_id_enc_encBinary`. -/
private theorem decidableInSubexpTime_of_encBinary
    {B : Set Instance} {μ : Instance → ℕ}
    (h : DecidableInSubexpTime B PartialMCSP.encBinary μ) :
    DecidableInSubexpTime B PartialMCSP.enc μ :=
  h.of_reduction computableInPolyTime_id_enc_encBinary (fun _ => Iff.rfl) (c := 1) fun _ => by simp

end PartialMCSP

namespace Complexity

open PartialMCSP Turing.MultiTapeTM

/-- **Ilango's ETH Lower Bound for `PartialMCSP` (unary threshold encoding)**
[Ilango2020FOCS, Theorem I.3, pp. 424, 427–428; ECCC TR20-183, Section 1.2.2, Theorem 3, p. 6, and
Section 3, Theorem 11, pp. 20–21]: under `ETH`, `PartialMCSP` on $m$-variable partial Boolean
functions cannot be decided in time $2^{o(m \log m)} = N^{o(\log \log N)}$ (where $N = 2^m$ is the
truth-table size). -/
theorem ETH.not_decidableInSubexpTime_PartialMCSP (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP PartialMCSP.enc
      fun I => I.arity * Nat.log 2 I.arity :=
  fun hsub => h.not_decidableInSubexpTime_BipartitePermutationIndependentSet
    (decidableInSubexpTime_bpis_of_ilangoReduction
      mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem hsub)

/-- **Ilango's ETH Lower Bound for `PartialMCSP` (binary threshold encoding)**
[Ilango2020FOCS, Theorem I.3, pp. 424, 427–428; ECCC TR20-183, Section 1.2.2, Theorem 3, p. 6, and
Section 3, Theorem 11, pp. 20–21]: under `ETH`, `PartialMCSP` on $m$-variable partial Boolean
functions cannot be decided in time $2^{o(m \log m)} = N^{o(\log \log N)}$ under binary threshold
encoding. -/
theorem ETH.not_decidableInSubexpTime_PartialMCSP_encBinary (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP PartialMCSP.encBinary
      fun I => I.arity * Nat.log 2 I.arity :=
  fun hsub => h.not_decidableInSubexpTime_PartialMCSP (decidableInSubexpTime_of_encBinary hsub)

/-- **Ilango's ETH Lower Bound for `PartialMCSP.BinaryGate` (unary threshold encoding)**
[Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183, Section 3, Theorem 11, pp. 20–21]: under
`ETH`, `PartialMCSP.BinaryGate` (circuit size measured by binary AND/OR gates) cannot be decided in
time $2^{o(m \log m)} = N^{o(\log \log N)}$. -/
theorem ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.BinaryGate PartialMCSP.enc
      fun I => I.arity * Nat.log 2 I.arity :=
  fun hsub => h.not_decidableInSubexpTime_BipartitePermutationIndependentSet
    (decidableInSubexpTime_bpis_of_ilangoReduction
      mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem_binaryGate hsub)

/-- **Ilango's ETH Lower Bound for `PartialMCSP.BinaryGate` (binary threshold encoding)**
[Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183, Section 3, Theorem 11, pp. 20–21]: under
`ETH`, `PartialMCSP.BinaryGate` cannot be decided in time $2^{o(m \log m)} = N^{o(\log \log N)}$
under binary threshold encoding. -/
theorem ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate_encBinary (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.BinaryGate PartialMCSP.encBinary
      fun I => I.arity * Nat.log 2 I.arity :=
  fun hsub =>
    h.not_decidableInSubexpTime_PartialMCSP_binaryGate (decidableInSubexpTime_of_encBinary hsub)

/-- **Ilango's ETH Lower Bound for `PartialMCSP.MonotoneReadOnce` (unary threshold encoding)**
[Ilango2020FOCS, Section III.B, p. 428; ECCC TR20-183, Section 3, Theorem 11, pp. 20–21]: under
`ETH`, even deciding whether a partial Boolean function has a monotone read-once formula of size at
most `threshold` cannot be done in time $2^{o(m \log m)} = N^{o(\log \log N)}$. -/
theorem ETH.not_decidableInSubexpTime_PartialMCSP_monotoneReadOnce (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.MonotoneReadOnce PartialMCSP.enc
      fun I => I.arity * Nat.log 2 I.arity :=
  fun hsub => h.not_decidableInSubexpTime_BipartitePermutationIndependentSet
    (decidableInSubexpTime_bpis_of_ilangoReduction
      mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem_monotoneReadOnce hsub)

/-- **Ilango's ETH Lower Bound for `PartialMCSP.MonotoneReadOnce` (binary threshold encoding)**
[Ilango2020FOCS, Section III.B, p. 428; ECCC TR20-183, Section 3, Theorem 11, pp. 20–21]: under
`ETH`, `PartialMCSP.MonotoneReadOnce` cannot be decided in time
$2^{o(m \log m)} = N^{o(\log \log N)}$ under binary threshold encoding. -/
theorem ETH.not_decidableInSubexpTime_PartialMCSP_monotoneReadOnce_encBinary (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.MonotoneReadOnce PartialMCSP.encBinary
      fun I => I.arity * Nat.log 2 I.arity :=
  fun hsub =>
    h.not_decidableInSubexpTime_PartialMCSP_monotoneReadOnce
      (decidableInSubexpTime_of_encBinary hsub)

/-- **Truth-table-size ($N = 2^m$) formulation of Ilango's ETH Lower Bound for `PartialMCSP`**
[Ilango2020FOCS, Theorem I.3, p. 424; ECCC TR20-183, Section 1.2.2, Theorem 3, p. 6]: under `ETH`,
`PartialMCSP` on partial truth tables of size $N = I.\text{tableSize} = 2^m$ is not decidable in
time $N^{o(\log \log N)} = 2^{o(\log_2 N \cdot \log_2 \log_2 N)}$. -/
theorem ETH.not_decidableInSubexpTime_PartialMCSP_tableSize (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP PartialMCSP.enc
      fun I => Nat.log 2 I.tableSize * Nat.log 2 (Nat.log 2 I.tableSize) := by
  simpa only [Instance.log_tableSize] using h.not_decidableInSubexpTime_PartialMCSP

/-- **Truth-table-size ($N = 2^m$) formulation of Ilango's ETH Lower Bound for `PartialMCSP`
(binary threshold encoding)** [Ilango2020FOCS, Theorem I.3, p. 424; ECCC TR20-183, Section 1.2.2,
Theorem 3, p. 6]: under `ETH`, `PartialMCSP` on partial truth tables of size
$N = I.\text{tableSize} = 2^m$ is not decidable in time
$N^{o(\log \log N)} = 2^{o(\log_2 N \cdot \log_2 \log_2 N)}$ under binary threshold encoding. -/
theorem ETH.not_decidableInSubexpTime_PartialMCSP_tableSize_encBinary (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP PartialMCSP.encBinary
      fun I => Nat.log 2 I.tableSize * Nat.log 2 (Nat.log 2 I.tableSize) :=
  fun hsub =>
    h.not_decidableInSubexpTime_PartialMCSP_tableSize (decidableInSubexpTime_of_encBinary hsub)

end Complexity
end Cslib
