/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.GraphProblems
import Complexity.Computability.Complexity.FineGrained.ExhaustiveSearch
import Complexity.Foundations.Data.BitString.List
import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/-!
# Bipartite Permutation Independent Set and its ETH lower bound

This module defines the `$2n \times 2n$ Bipartite Permutation Independent Set` problem and proves
the Lokshtanov–Marx–Saurabh lower bound under the Exponential Time Hypothesis (`ETH`): the problem
cannot be decided in time $2^{o(n \log n)}$ [LokshtanovMarxSaurabh2018, Theorem 2.11], as used in
Ilango's reduction to partial-function MCSP [Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183,
Section 3, Theorem 10, p. 20].

## Formulations and faithfulness

Two equivalent presentations appear in the literature:

1. **Ilango's directed pair formulation** [Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183,
   Section 3, Theorem 10, p. 20]: an instance `G : BipartitePermutationGraph` consists of a
   parameter $n = G.1$ and a list $G.2$ of directed edges $((u_1, u_2), (v_1, v_2))$ on
   $[n] \times [n]$. It is a yes-instance (`G ∈ BipartitePermutationIndependentSet`) when there
   exist two permutations $\pi_1, \pi_2 \in S_n$ (`Equiv.Perm (Fin G.1)`) such that for no edge
   $((u_1, u_2), (v_1, v_2)) \in G.2$ do we simultaneously have $\pi_1(u_1) = u_2$ and
   $\pi_2(v_1) = v_2$ (`BipartitePermutationGraph.Satisfies`).
2. **Lokshtanov–Marx–Saurabh's undirected bipartite permutation formulation**
   [LokshtanovMarxSaurabh2018, Section 2.2, Theorem 2.11]: a single permutation
   $\pi \in S_{2n}$ (`Equiv.Perm (Fin (2 * G.1))`) preserves the two blocks $[0, n)$ and
   $[n, 2n)$ (`BipartitePermutationGraph.IsBlockPreserving`) and avoids every undirected conflict
   between $(u_1, u_2)$ in the first half and $(n + v_1, n + v_2)$ in the second half
   (`BipartitePermutationGraph.SatisfiesUndirected`).

`BipartitePermutationGraph.exists_satisfies_iff_exists_satisfiesUndirected` and
`BipartitePermutationIndependentSet.mem_iff_exists_satisfiesUndirected` prove that the two
formulations define the exact same language.

## Proof of the ETH lower bound

To prove [LokshtanovMarxSaurabh2018, Theorem 2.11], this library gives a direct Turing reduction
from `ThreeColoring` on $N$-vertex graphs (which has no $2^{o(N)}$-time algorithm under `ETH` by
`ETH.not_decidableInSubexpTime_ThreeColoring_vertices`) to subexponentially many instances of
`BipartitePermutationIndependentSet` of parameter $n = \Theta(N / \log N)$, for which
$n \log_2 n \le 10 N + 5$ (`BipartitePermutationIndependentSet.fst_bpisOfColoring_mul_log_le`),
using a library proof based on monotone threshold enumeration (`Tuple.sort` and
`Tuple.lt_card_le_iff_apply_le_of_monotone`):

* Partition the $N$ vertices into $n = \lfloor N / b \rfloor + 1$ blocks of size
  $b = \lfloor (\log_2 N) / 4 \rfloor + 1$, so that $n \log_2 n \le 10 N + 5$
  (`BipartitePermutationIndependentSet.fst_bpisOfColoring_mul_log_le`).
* A 3-coloring of a block is encoded by $2b$ bits as a number below $B = 2^{2b} = 4^b$, so a
  3-coloring of the graph induces a tuple $a : \mathrm{Fin}\, n \to \mathrm{Fin}\, B$.
* By `Tuple.sort`, any tuple $a : \mathrm{Fin}\, n \to \mathrm{Fin}\, B$ factors as
  $a = \beta \circ \pi$ where $\beta = a \circ \mathrm{Tuple.sort}\, a$ is monotone nondecreasing
  and $\pi = (\mathrm{Tuple.sort}\, a)^{-1} \in S_n$.
* A monotone function $\beta : \mathrm{Fin}\, n \to \mathrm{Fin}\, B$ is uniquely determined by the
  $B$ threshold counts $t_v = |\{j < n \mid \beta(j) \le v\}| \in \{0, \ldots, n\}$ via
  `Tuple.lt_card_le_iff_apply_le_of_monotone`, encoded in $B \cdot (\lfloor \log_2 n \rfloor + 1) =
  o(N)$ bits.
* Branching over all $2^{B \cdot (\lfloor \log_2 n \rfloor + 1)} = 2^{o(N)}$ threshold encodings
  and querying a purported $2^{o(n \log n)}$ decider for `BipartitePermutationIndependentSet`
  decides `ThreeColoring` in time $2^{o(N)}$, contradicting `ETH`.

## Main definitions

* `Cslib.Complexity.BipartitePermutationGraph`: instance $(n, E)$ of parameter $n$ and directed
  pair-edges $E$.
* `Cslib.Complexity.encBipartitePermutationGraph`,
  `Cslib.Complexity.encBipartitePermutationGraphBinary`: unary and binary encodings.
* `Cslib.Complexity.BipartitePermutationGraph.Satisfies`: Ilango's two-permutation predicate.
* `Cslib.Complexity.BipartitePermutationGraph.IsBlockPreserving`,
  `Cslib.Complexity.BipartitePermutationGraph.SatisfiesUndirected`: Lokshtanov–Marx–Saurabh's
  block-preserving single-permutation predicate on $\mathrm{Fin}\,(2n)$.
* `Cslib.Complexity.BipartitePermutationIndependentSet`: the language of satisfiable instances.
* `Cslib.Complexity.BipartitePermutationIndependentSet.searchBits`,
  `Cslib.Complexity.BipartitePermutationIndependentSet.bpisOfColoring`: threshold-table bit length
  and the block-sorting reduction from `ThreeColoring`.

## Main results

* `Cslib.Complexity.BipartitePermutationGraph.exists_satisfies_iff_exists_satisfiesUndirected`,
  `Cslib.Complexity.BipartitePermutationIndependentSet.mem_iff_exists_satisfiesUndirected`:
  equivalence of Ilango's and Lokshtanov–Marx–Saurabh's formulations.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_ThreeColoring_vertices`: under `ETH`,
  `ThreeColoring` is not decidable in time $2^{o(|V|)}$.
* `Cslib.Complexity.BipartitePermutationIndependentSet.mem_ThreeColoring_iff_exists_bpisOfColoring`:
  correctness of the block-sorting reduction from `ThreeColoring` to
  `BipartitePermutationIndependentSet`.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet`: under `ETH`,
  `BipartitePermutationIndependentSet` is not decidable in time $2^{o(n \log n)}$
  ([LokshtanovMarxSaurabh2018, Theorem 2.11]; [Ilango2020FOCS, Section III.B, p. 427; ECCC
  TR20-183, Section 3, Theorem 10, p. 20]).
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet_binary`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet_clog`,
  `Cslib.Complexity.ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet_two_mul`:
  variants for binary encoding, ceiling logarithm $n \lceil \log_2 n \rceil$, and parameter
  $2n \log_2(2n)$.

## References

* [R. Ilango, *Constant Depth Formula and Partial Function Versions of MCSP are
  Hard*][Ilango2020FOCS]
* [D. Lokshtanov, D. Marx, S. Saurabh, *Lower bounds based on the Exponential Time
  Hypothesis*][LokshtanovMarxSaurabh2011]
* [D. Lokshtanov, D. Marx, S. Saurabh, *Slightly Superexponential Parameterized
  Problems*][LokshtanovMarxSaurabh2018]
-/

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

public section

/-! ### Problem definitions and equivalence of formulations -/

/-- An instance of `$2n \times 2n$ Bipartite Permutation Independent Set`
[Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183, Section 3, Theorem 10, p. 20]: a parameter
$n$ together with a list of directed edges $((u_1, u_2), (v_1, v_2))$ between vertex pairs in
$[n] \times [n]$. -/
abbrev BipartitePermutationGraph : Type := ℕ × List ((ℕ × ℕ) × (ℕ × ℕ))

/-- Unary encoding of a `BipartitePermutationGraph`, matching Ilango's presentation in which the
graph has $O(n^2)$ vertices and coordinates are bounded by $n$
[Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183, Section 3, p. 20]. -/
@[expose] def encBipartitePermutationGraph : BipartitePermutationGraph ↪ List Bool :=
  encPair encUnary (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)))

/-- Binary encoding of a `BipartitePermutationGraph`. -/
@[expose] def encBipartitePermutationGraphBinary : BipartitePermutationGraph ↪ List Bool :=
  encPair encNat (encList (encPair (encPair encNat encNat) (encPair encNat encNat)))

namespace BipartitePermutationGraph

/-- **Ilango's directed satisfaction predicate** [Ilango2020FOCS, Section III.B, p. 427; ECCC
TR20-183, Section 3, Theorem 10, p. 20]: two permutations $\pi_1, \pi_2 \in S_n$ satisfy $G$ when
for no edge $((u_1, u_2), (v_1, v_2)) \in G.2$ with coordinates below $n = G.1$ do we have both
$\pi_1(u_1) = u_2$ and $\pi_2(v_1) = v_2$. -/
@[expose] def Satisfies (G : BipartitePermutationGraph) (π₁ π₂ : Equiv.Perm (Fin G.1)) : Prop :=
  ∀ e ∈ G.2, ∀ (hu₁ : e.1.1 < G.1) (hu₂ : e.1.2 < G.1) (hv₁ : e.2.1 < G.1) (hv₂ : e.2.2 < G.1),
    π₁ ⟨e.1.1, hu₁⟩ = ⟨e.1.2, hu₂⟩ → π₂ ⟨e.2.1, hv₁⟩ ≠ ⟨e.2.2, hv₂⟩

/-- A permutation of $\mathrm{Fin}\,(2n)$ is **block-preserving** when it maps the first half
$[0, n)$ to $[0, n)$ (and hence the second half $[n, 2n)$ to $[n, 2n)$)
[LokshtanovMarxSaurabh2018, Theorem 2.11]. -/
@[expose] def IsBlockPreserving {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) : Prop :=
  ∀ i : Fin (2 * n), i.val < n ↔ (π i).val < n

/-- **Lokshtanov–Marx–Saurabh's undirected bipartite satisfaction predicate**
[LokshtanovMarxSaurabh2018, Section 2.2, Theorem 2.11]: a single permutation
$\pi \in S_{2n}$ preserves the two blocks $[0, n)$ and $[n, 2n)$ and for no conflict edge
$((u_1, u_2), (v_1, v_2)) \in G.2$ between the two blocks do we have both $\pi(u_1) = u_2$ and
$\pi(n + v_1) = n + v_2$. -/
@[expose] def SatisfiesUndirected (G : BipartitePermutationGraph)
    (π : Equiv.Perm (Fin (2 * G.1))) : Prop :=
  IsBlockPreserving π ∧
    ∀ e ∈ G.2, ∀ (hu₁ : e.1.1 < G.1) (_hu₂ : e.1.2 < G.1) (hv₁ : e.2.1 < G.1) (_hv₂ : e.2.2 < G.1),
      (π ⟨e.1.1, by omega⟩).val = e.1.2 → (π ⟨G.1 + e.2.1, by omega⟩).val ≠ G.1 + e.2.2

theorem IsBlockPreserving.symm {n : ℕ} {π : Equiv.Perm (Fin (2 * n))}
    (hπ : IsBlockPreserving π) : IsBlockPreserving π.symm := by
  intro i
  simpa only [π.apply_symm_apply] using (hπ (π.symm i)).symm

/-- The block-splitting equivalence $\mathrm{Fin}\, n \oplus \mathrm{Fin}\, n \simeq
\mathrm{Fin}\,(2n)$. -/
private def blockEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (two_mul n).symm)

/-- Combining two permutations $\pi_1, \pi_2 \in S_n$ on the two halves of $\mathrm{Fin}\,(2n)$. -/
def combinePerm {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (2 * n)) :=
  (blockEquiv n).permCongr (Equiv.Perm.sumCongr π₁ π₂)

@[simp] theorem combinePerm_inl {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n)) (i : Fin n) :
    (combinePerm π₁ π₂ ⟨i.val, by omega⟩).val = (π₁ i).val := by
  have h : (⟨i.val, by omega⟩ : Fin (2 * n)) = blockEquiv n (Sum.inl i) := by
    ext; simp [blockEquiv]
  rw [h, combinePerm, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  simp [blockEquiv]

@[simp] theorem combinePerm_inr {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n)) (i : Fin n) :
    (combinePerm π₁ π₂ ⟨n + i.val, by omega⟩).val = n + (π₂ i).val := by
  have h : (⟨n + i.val, by omega⟩ : Fin (2 * n)) = blockEquiv n (Sum.inr i) := by
    ext; simp only [blockEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finSumFinEquiv_apply_right, Fin.val_natAdd]
  rw [h, combinePerm, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  simp only [Equiv.Perm.sumCongr_apply, Sum.map_inr, blockEquiv, Equiv.trans_apply,
    finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd]

theorem isBlockPreserving_combinePerm {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n)) :
    IsBlockPreserving (combinePerm π₁ π₂) := by
  intro i
  by_cases h : i.val < n
  · have hi : i = ⟨(⟨i.val, h⟩ : Fin n).val, by omega⟩ := rfl
    rw [hi, combinePerm_inl]
    exact ⟨fun _ => (π₁ ⟨i.val, h⟩).isLt, fun _ => h⟩
  · let j : Fin n := ⟨i.val - n, by omega⟩
    have hi : i = ⟨n + j.val, by omega⟩ := by ext; dsimp only [j]; omega
    rw [hi, combinePerm_inr]
    exact ⟨fun hlt => absurd (hi ▸ hlt) h, fun hlt => by omega⟩

/-- Extracting the first-half permutation on $\mathrm{Fin}\, n$ from a block-preserving permutation
of $\mathrm{Fin}\,(2n)$. -/
def fstPerm {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) (hπ : IsBlockPreserving π) :
    Equiv.Perm (Fin n) where
  toFun i := ⟨(π ⟨i.val, by omega⟩).val, (hπ ⟨i.val, by omega⟩).mp i.isLt⟩
  invFun i := ⟨(π.symm ⟨i.val, by omega⟩).val, (hπ.symm ⟨i.val, by omega⟩).mp i.isLt⟩
  left_inv i := by ext; simp [Fin.eta]
  right_inv i := by ext; simp [Fin.eta]

private def sndPermFun {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) (hπ : IsBlockPreserving π)
    (i : Fin n) : Fin n :=
  ⟨(π ⟨n + i.val, by omega⟩).val - n, by
    have := mt (hπ ⟨n + i.val, by omega⟩).mpr (by simp)
    have := (π ⟨n + i.val, by omega⟩).isLt
    omega⟩

private theorem sndPermFun_left_inv {n : ℕ} {π : Equiv.Perm (Fin (2 * n))}
    (hπ : IsBlockPreserving π) (i : Fin n) :
    sndPermFun π.symm hπ.symm (sndPermFun π hπ i) = i := by
  ext
  dsimp only [sndPermFun]
  have hge : n ≤ (π ⟨n + i.val, by omega⟩).val :=
    Nat.le_of_not_lt (mt (hπ ⟨n + i.val, by omega⟩).mpr (by simp))
  have heq : (⟨n + ((π ⟨n + i.val, by omega⟩).val - n), by omega⟩ : Fin (2 * n)) =
      π ⟨n + i.val, by omega⟩ := by ext; dsimp only; omega
  rw [heq, π.symm_apply_apply]
  dsimp only
  omega

/-- Extracting the second-half permutation on $\mathrm{Fin}\, n$ from a block-preserving permutation
of $\mathrm{Fin}\,(2n)$. -/
def sndPerm {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) (hπ : IsBlockPreserving π) :
    Equiv.Perm (Fin n) where
  toFun := sndPermFun π hπ
  invFun := sndPermFun π.symm hπ.symm
  left_inv := sndPermFun_left_inv hπ
  right_inv := sndPermFun_left_inv hπ.symm

/-- **Equivalence of Ilango's and Lokshtanov–Marx–Saurabh's formulations**: an instance $G$ is
satisfied by a pair of permutations $\pi_1, \pi_2 \in S_n$ if and only if it is satisfied by a
block-preserving permutation $\pi \in S_{2n}$. -/
theorem exists_satisfies_iff_exists_satisfiesUndirected (G : BipartitePermutationGraph) :
    (∃ π₁ π₂ : Equiv.Perm (Fin G.1), G.Satisfies π₁ π₂) ↔
      ∃ π : Equiv.Perm (Fin (2 * G.1)), G.SatisfiesUndirected π := by
  constructor
  · rintro ⟨π₁, π₂, hG⟩
    refine ⟨combinePerm π₁ π₂, isBlockPreserving_combinePerm π₁ π₂,
      fun e he hu₁ hu₂ hv₁ hv₂ h1 h2 => ?_⟩
    rw [combinePerm_inl π₁ π₂ ⟨e.1.1, hu₁⟩] at h1
    rw [combinePerm_inr π₁ π₂ ⟨e.2.1, hv₁⟩] at h2
    exact hG e he hu₁ hu₂ hv₁ hv₂ (Fin.ext h1) (Fin.ext (Nat.add_left_cancel h2))
  · rintro ⟨π, hblock, hG⟩
    refine ⟨fstPerm π hblock, sndPerm π hblock, fun e he hu₁ hu₂ hv₁ hv₂ h1 h2 => ?_⟩
    have h1' : (π ⟨e.1.1, by omega⟩).val = e.1.2 := congrArg Fin.val h1
    have h2' : (π ⟨G.1 + e.2.1, by omega⟩).val - G.1 = e.2.2 := congrArg Fin.val h2
    have hnot : ¬(⟨G.1 + e.2.1, by omega⟩ : Fin (2 * G.1)).val < G.1 := by simp
    have hge : G.1 ≤ (π ⟨G.1 + e.2.1, by omega⟩).val :=
      Nat.le_of_not_lt (mt (hblock ⟨G.1 + e.2.1, by omega⟩).mpr hnot)
    exact hG e he hu₁ hu₂ hv₁ hv₂ h1' (by omega)

end BipartitePermutationGraph

/-- **$2n \times 2n$ Bipartite Permutation Independent Set**
[Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183, Section 3, Theorem 10, p. 20]
[LokshtanovMarxSaurabh2018, Section 2.2, Theorem 2.11]:
the set of instances $G = (n, E)$ admitting permutations $\pi_1, \pi_2 \in S_n$ that avoid all
conflict edges in $E$. -/
@[expose] def BipartitePermutationIndependentSet : Set BipartitePermutationGraph :=
  {G | ∃ π₁ π₂ : Equiv.Perm (Fin G.1), G.Satisfies π₁ π₂}

/-- Equivalence between the two-permutation bipartite formulation of the Bipartite Permutation
Independent Set problem and the single-permutation undirected formulation of
[LokshtanovMarxSaurabh2018, Section 2.2]. -/
theorem BipartitePermutationIndependentSet.mem_iff_exists_satisfiesUndirected
    (G : BipartitePermutationGraph) :
    G ∈ BipartitePermutationIndependentSet ↔
      ∃ π : Equiv.Perm (Fin (2 * G.1)), G.SatisfiesUndirected π :=
  G.exists_satisfies_iff_exists_satisfiesUndirected

/-! ### Three-coloring indexed by vertex positions and ETH lower bound in `|V|` -/

/-- Membership in `ThreeColoring` is equivalent to a proper 3-coloring of the vertex positions
`Fin G.1.length` with respect to `G.adjBool`. -/
theorem mem_ThreeColoring_iff_fin (G : Graph) :
    G ∈ ThreeColoring ↔ ∃ f : Fin G.1.length → Fin 3,
      ∀ p q : Fin G.1.length, G.adjBool G.1[p] G.1[q] = true → f p ≠ f q := by
  classical
  rw [ThreeColoring, mem_KColoring_iff]
  constructor
  · rintro ⟨c, hc, hadj⟩
    refine ⟨fun p => ⟨c G.1[p], hc G.1[p] (List.getElem_mem p.isLt)⟩, fun p q hpq h => ?_⟩
    rw [Graph.adjBool_eq_true_iff] at hpq
    exact hadj G.1[p] (List.getElem_mem p.isLt) G.1[q] (List.getElem_mem q.isLt) hpq
      (congrArg Fin.val h)
  · rintro ⟨f, hf⟩
    refine ⟨fun u =>
        if hu : u ∈ G.1 then (f ⟨G.1.idxOf u, List.idxOf_lt_length_iff.2 hu⟩).val else 0,
      fun v hv => by
        dsimp only
        simp only [hv, ↓reduceDIte]
        exact (f _).isLt,
      fun u hu v hv huv h => ?_⟩
    dsimp only at h
    simp only [hu, hv, ↓reduceDIte] at h
    have hu' : G.1.idxOf u < G.1.length := List.idxOf_lt_length_iff.2 hu
    have hv' : G.1.idxOf v < G.1.length := List.idxOf_lt_length_iff.2 hv
    have hpq : G.adjBool G.1[G.1.idxOf u] G.1[G.1.idxOf v] = true := by
      simpa only [List.getElem_idxOf, Graph.adjBool_eq_true_iff] using huv
    exact hf ⟨G.1.idxOf u, hu'⟩ ⟨G.1.idxOf v, hv'⟩ hpq (Fin.ext h)

/-- **No $2^{o(|V|)}$ algorithm for 3-coloring under ETH** [CyganEtAl2015, Chapter 14]:
for some $\delta > 0$, `ThreeColoring` is not decidable within time $2^{\delta |V|}$ times any
polynomial in the length of the encoded graph, for graphs with $|V|$ declared vertices. -/
theorem ETH.not_decidableInSubexpTime_ThreeColoring_vertices (h : ETH) :
    ¬DecidableInSubexpTime ThreeColoring encGraph fun G => G.1.length :=
  h.not_decidableInSubexpTime_of_reduction SAT.computableInPolyTime_toThreeColoring
    (fun φ _ => SAT.toThreeColoring_mem_iff φ) (k := 93) fun φ hφ => by
      have := SAT.length_toThreeColoring_le hφ
      nlinarith

/-! ### Block parameters and arithmetic bounds for the LMS reduction -/

namespace BipartitePermutationIndependentSet

/-- Block size $b = \lfloor (\log_2 N) / 4 \rfloor + 1$ for grouping $N$ vertices. -/
private def blockSize (N : ℕ) : ℕ := Nat.log 2 N / 4 + 1

/-- Number of $2b$-bit block-coloring assignments $B = 2^{2b} = 4^b$. -/
private def numAssignments (N : ℕ) : ℕ := 2 ^ (2 * blockSize N)

/-- Number of vertex blocks $n = \lfloor N / b \rfloor + 1$. -/
private def numBlocks (N : ℕ) : ℕ := N / blockSize N + 1

/-- Bit-width $L = \lfloor \log_2 n \rfloor + 1$ of each threshold count in $\{0, \ldots, n\}$. -/
private def wordLen (N : ℕ) : ℕ := Nat.log 2 (numBlocks N) + 1

/-- Total number of bits $K = B \cdot L$ in a threshold table. -/
def searchBits (N : ℕ) : ℕ := numAssignments N * wordLen N

private theorem blockSize_pos (N : ℕ) : 0 < blockSize N := Nat.succ_pos _

private theorem numBlocks_pos (N : ℕ) : 0 < numBlocks N := Nat.succ_pos _

private theorem div_blockSize_lt_numBlocks {N p : ℕ} (hp : p < N) :
    p / blockSize N < numBlocks N := by
  have := Nat.div_le_div_right hp.le (c := blockSize N)
  unfold numBlocks
  omega

private theorem numBlocks_lt_two_pow_wordLen (N : ℕ) : numBlocks N < 2 ^ wordLen N :=
  Nat.lt_pow_succ_log_self Nat.one_lt_two (numBlocks N)

private theorem blockSize_le (N : ℕ) : blockSize N ≤ N + 1 := by
  have := Nat.log_le_self 2 N
  unfold blockSize
  omega

private theorem numBlocks_le (N : ℕ) : numBlocks N ≤ N + 1 := by
  have := Nat.div_le_self N (blockSize N)
  unfold numBlocks
  omega

private theorem log_numBlocks_le (N : ℕ) : Nat.log 2 (numBlocks N) ≤ 5 * blockSize N := by
  have hlog : Nat.log 2 N + 1 ≤ 4 * blockSize N := by
    unfold blockSize
    omega
  have hN : N < 2 ^ (4 * blockSize N) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two N).trans_le
      (Nat.pow_le_pow_right two_pos hlog)
  have hpow : 2 ^ (4 * blockSize N) < 2 ^ (5 * blockSize N) :=
    Nat.pow_lt_pow_right Nat.one_lt_two (by have := blockSize_pos N; omega)
  have hnb : numBlocks N < 2 ^ (5 * blockSize N) := by
    have := numBlocks_le N
    omega
  exact (Nat.log_lt_of_lt_pow (numBlocks_pos N).ne' hnb).le

private theorem numBlocks_mul_log_le (N : ℕ) :
    numBlocks N * Nat.log 2 (numBlocks N) ≤ 10 * N + 5 := by
  have hlog := log_numBlocks_le N
  have hdiv : N / blockSize N * blockSize N ≤ N := Nat.div_mul_le_self N (blockSize N)
  have hbs := blockSize_le N
  calc numBlocks N * Nat.log 2 (numBlocks N)
      ≤ (N / blockSize N + 1) * (5 * blockSize N) := Nat.mul_le_mul_left _ hlog
    _ = 5 * (N / blockSize N * blockSize N) + 5 * blockSize N := by ring
    _ ≤ 5 * N + 5 * (N + 1) := by omega
    _ = 10 * N + 5 := by ring

private theorem numAssignments_le (N : ℕ) : numAssignments N ≤ 4 * N + 4 := by
  set k := Nat.log 2 N / 4
  have h2k : 2 * k ≤ Nat.log 2 N := by omega
  have hpow : 2 ^ (2 * k) ≤ N + 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [k]
    · exact (Nat.pow_le_pow_right two_pos h2k).trans
        ((Nat.pow_log_le_self 2 (by omega)).trans (Nat.le_succ N))
  have heq : numAssignments N = 4 * 2 ^ (2 * k) := by
    unfold numAssignments blockSize
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    ring
  omega

private theorem wordLen_le (N : ℕ) : wordLen N ≤ 6 * blockSize N := by
  have hlog := log_numBlocks_le N
  have hbs := blockSize_pos N
  unfold wordLen
  omega

/-- **Sublinear search-exponent bound**: for every $M \ge 1$, the number of threshold bits is at
most $N / M + 48 \cdot (48 M)^3$. -/
theorem searchBits_le_div_add (N : ℕ) {M : ℕ} (hM : 0 < M) :
    searchBits N ≤ N / M + 48 * (48 * M) ^ 3 := by
  set k := Nat.log 2 N / 4
  have hA : numAssignments N = 4 * (2 ^ k) ^ 2 := by
    unfold numAssignments blockSize
    rw [show 2 * (k + 1) = k * 2 + 2 by ring, pow_add, pow_mul]
    ring
  have hW : wordLen N ≤ 12 * 2 ^ k := by
    have h1 : wordLen N ≤ 6 * (k + 1) := wordLen_le N
    have h2 : k + 1 ≤ 2 ^ (k + 1) := (Nat.lt_two_pow_self (n := k + 1)).le
    calc wordLen N ≤ 6 * (k + 1) := h1
      _ ≤ 6 * 2 ^ (k + 1) := Nat.mul_le_mul_left 6 h2
      _ = 12 * 2 ^ k := by rw [pow_succ]; ring
  have hSB : searchBits N ≤ 48 * (2 ^ k) ^ 3 := by
    calc searchBits N = numAssignments N * wordLen N := rfl
      _ ≤ 4 * (2 ^ k) ^ 2 * (12 * 2 ^ k) := by rw [hA]; exact Nat.mul_le_mul_left _ hW
      _ = 48 * (2 ^ k) ^ 3 := by ring
  by_cases hk : 2 ^ k ≤ 48 * M
  · have hcube : (2 ^ k) ^ 3 ≤ (48 * M) ^ 3 := Nat.pow_le_pow_left hk 3
    exact (hSB.trans (Nat.mul_le_mul_left 48 hcube)).trans (Nat.le_add_left _ _)
  · have hk' : 48 * M < 2 ^ k := Nat.lt_of_not_le hk
    have hN0 : N ≠ 0 := by
      rintro rfl
      have hk0 : 2 ^ k = 1 := by decide
      omega
    have h4k : 4 * k ≤ Nat.log 2 N := by omega
    have hpow4 : (2 ^ k) ^ 4 ≤ N := by
      calc (2 ^ k) ^ 4 = 2 ^ (4 * k) := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right two_pos h4k
        _ ≤ N := Nat.pow_log_le_self 2 hN0
    have hmul : 48 * (2 ^ k) ^ 3 * M ≤ N := by
      calc 48 * (2 ^ k) ^ 3 * M = 48 * M * (2 ^ k) ^ 3 := by ring
        _ ≤ 2 ^ k * (2 ^ k) ^ 3 := Nat.mul_le_mul_right _ hk'.le
        _ = (2 ^ k) ^ 4 := by ring
        _ ≤ N := hpow4
    have hdiv : 48 * (2 ^ k) ^ 3 ≤ N / M := (Nat.le_div_iff_mul_le hM).2 hmul
    exact (hSB.trans hdiv).trans (Nat.le_add_right _ _)

/-! ### Block-coloring extraction, threshold decoding, and `bpisOfColoring` -/

/-- Extract the 2-bit color in $\{0, 1, 2, 3\}$ of local vertex offset $u$ from a block assignment
number $c$. -/
private def extractColor (c u : ℕ) : ℕ :=
  (c.testBit (2 * u)).toNat + 2 * (c.testBit (2 * u + 1)).toNat

/-- Check whether a block assignment number $c$ assigns a valid color in $\{0, 1, 2\}$ to every
offset $u < b$. -/
private def validAssignment (b c : ℕ) : Bool :=
  (List.range b).all fun u => decide (extractColor c u < 3)

/-- Decode the $v$-th threshold count from the binary digits of $r$, as an $L$-bit word capped at
$n$. -/
private def thresholdOf (n L r v : ℕ) : ℕ :=
  Cslib.BitString.boundedBinaryValue n (Cslib.BitString.listRow L v r.bits)

/-- Reconstruct the sorted block assignment $\beta(j) \in \{0, \ldots, B - 1\}$ at sorted position
$j$ from the decoded thresholds: $\beta(j)$ is the number of values $v < B - 1$ whose threshold
$t_v = |\{k < n \mid \beta(k) \le v\}|$ is at most $j$. -/
private def bucketOf (B n L r j : ℕ) : ℕ :=
  (List.range (B - 1)).countP fun v => decide (thresholdOf n L r v ≤ j)

/-- The color assigned to local offset $u$ by the $j$-th sorted bucket under threshold table $r$. -/
private def colorAt (N r j u : ℕ) : ℕ :=
  extractColor (bucketOf (numAssignments N) (numBlocks N) (wordLen N) r j) u

/-- Edges enforcing $\pi_1(i) = \pi_2(i)$ for all $i < n$. -/
private def consistencyEdges (n : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (List.range n).flatMap fun i =>
    (List.range n).flatMap fun j₁ =>
      ((List.range n).filter fun j₂ => !decide (j₁ = j₂)).map fun j₂ => ((i, j₁), (i, j₂))

/-- Self-edges forbidding $\pi_1(i) = j$ when bucket $j$ is not a valid 3-coloring of a block. -/
private def invalidBucketEdges (N r : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let b := blockSize N
  let B := numAssignments N
  let n := numBlocks N
  let L := wordLen N
  (List.range n).flatMap fun i =>
    ((List.range n).filter fun j => !validAssignment b (bucketOf B n L r j)).map fun j =>
      ((i, j), (i, j))

/-- Test whether bucket pair $(j_1, j_2)$ creates a color conflict for vertex pair $(p, q)$. -/
private def innerConflictTest (N r p q j₁ j₂ : ℕ) : Bool :=
  let b := blockSize N
  let i₁ := p / b
  let u₁ := p % b
  let i₂ := q / b
  let u₂ := q % b
  (!decide (i₁ = i₂) || decide (j₁ = j₂)) &&
    decide (colorAt N r j₁ u₁ = colorAt N r j₂ u₂)

/-- Filtered second-bucket indices $j_2 < n$ that conflict with $(p, q, j_1)$. -/
private def innerConflictBuckets (N r p q j₁ : ℕ) : List ℕ :=
  (List.range (numBlocks N)).filter (innerConflictTest N r p q j₁)

/-- Conflict edges for a fixed vertex pair $(p, q)$ and first bucket index $j_1$. -/
private def innerConflictEdges (N r p q j₁ : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let b := blockSize N
  let i₁ := p / b
  let i₂ := q / b
  (innerConflictBuckets N r p q j₁).map fun j₂ =>
    ((i₁, j₁), (i₂, j₂))

/-- Conflict edges for a fixed vertex pair $(p, q)$ across all bucket pairs $(j_1, j_2)$. -/
private def pairConflictEdges (N r p q : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (List.range (numBlocks N)).flatMap fun j₁ => innerConflictEdges N r p q j₁

/-- Conflict edges incident to vertex position $p$ across all adjacent vertex positions $q$. -/
private def vertexConflictEdges (H : Graph) (r p : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let N := H.1.length
  ((List.range N).filter fun q => H.adjBool (H.1.getD p 0) (H.1.getD q 0)).flatMap fun q =>
    pairConflictEdges N r p q

/-- Edges forbidding adjacent vertices $p, q < N$ of $H$ from receiving the same color under the
block assignments selected by $\pi_1(p / b) = j_1$ and $\pi_2(q / b) = j_2$. -/
private def conflictEdges (H : Graph) (r : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (List.range H.1.length).flatMap fun p => vertexConflictEdges H r p

/-- The instance of `BipartitePermutationIndependentSet` corresponding to a graph $H$ and a
threshold-table number $r$. -/
def bpisOfColoring (x : Graph × ℕ) : BipartitePermutationGraph :=
  let N := x.1.1.length
  (numBlocks N, consistencyEdges (numBlocks N) ++ invalidBucketEdges N x.2 ++ conflictEdges x.1 x.2)

/-- **Parameter bound**: the output parameter $n = (\mathrm{bpisOfColoring}\,(H, r)).1$ satisfies
$n \log_2 n \le 10 |V| + 5$. -/
theorem fst_bpisOfColoring_mul_log_le (H : Graph) (r : ℕ) :
    (bpisOfColoring (H, r)).1 * Nat.log 2 (bpisOfColoring (H, r)).1 ≤ 10 * H.1.length + 5 :=
  numBlocks_mul_log_le H.1.length

@[simp] theorem bpisOfColoring_empty_zero :
    bpisOfColoring (([], []), 0) = (1, [((0, 0), (0, 0))]) := by
  decide

/-! ### Correctness of the reduction -/

private theorem countP_range_lt {m k : ℕ} (hk : k ≤ m) :
    ((List.range m).countP fun v => decide (v < k)) = k := by
  induction m with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ m ih =>
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rw [List.countP_eq_length_filter, List.filter_eq_self.2 (by simp), List.length_range]
    · rw [List.range_succ, List.countP_append, ih (Nat.le_of_lt_succ hlt)]
      simp [Nat.not_lt.2 (Nat.le_of_lt_succ hlt)]

open Finset in
/-- Every tuple $a : \mathrm{Fin}\, n \to \mathrm{Fin}\, B$ has a threshold number
$r < 2^{\mathrm{searchBits}\, N}$ from which `bucketOf` recovers the sorted tuple
$a \circ \mathrm{Tuple.sort}\, a$. -/
private theorem exists_bucketOf_eq_sort (N : ℕ)
    (a : Fin (numBlocks N) → Fin (numAssignments N)) :
    ∃ r < 2 ^ searchBits N, ∀ j : Fin (numBlocks N),
      bucketOf (numAssignments N) (numBlocks N) (wordLen N) r j.val =
        (a (Tuple.sort a j)).val := by
  let B := numAssignments N
  let n := numBlocks N
  let L := wordLen N
  let β : Fin n → Fin B := a ∘ Tuple.sort a
  have hβ_mono : Monotone (fun j : Fin n => (β j).val) :=
    fun i j hij => Tuple.monotone_sort a hij
  let t : ℕ → ℕ := fun v => #{k : Fin n | (β k).val ≤ v}
  have ht_le (v : ℕ) : t v ≤ n := by
    simpa only [t, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun k : Fin n => (β k).val ≤ v)
  have ht_lt (v : ℕ) : t v < 2 ^ L := (ht_le v).trans_lt (numBlocks_lt_two_pow_wordLen N)
  have ht_iff (j : Fin n) (v : ℕ) : t v ≤ j.val ↔ v < (β j).val := by
    have h := Tuple.lt_card_le_iff_apply_le_of_monotone (j := j) (a := v) hβ_mono
    dsimp only [t]
    omega
  let w : List Bool := (List.range B).flatMap fun v => Cslib.BitString.binaryWord L (t v)
  have hw_len : w.length = searchBits N := by
    have h1 : ∀ v ∈ List.range B, (Cslib.BitString.binaryWord L (t v)).length = L :=
      fun v _ => Cslib.BitString.length_binaryWord (ht_lt v)
    simp only [w, List.length_flatMap, List.map_congr_left h1, List.map_const',
      List.length_range, List.sum_replicate, smul_eq_mul, searchBits, B, L]
  let r : ℕ := (BitVec.ofBoolListLE w).toNat
  have hr_lt : r < 2 ^ searchBits N := by
    simpa only [r, hw_len] using (BitVec.isLt (BitVec.ofBoolListLE w))
  have hr_bit (idx : ℕ) : r.bits.getD idx false = w.getD idx false := by
    change r.bits.getI idx = w.getD idx false
    rw [← Nat.testBit_eq_inth, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  have hthresh (v : ℕ) (hv : v < B) : thresholdOf n L r v = t v := by
    have hrow : Cslib.BitString.listRow L v r.bits = Cslib.BitString.listRow L v w := by
      refine List.ext_getElem (by simp) fun i hi _ => ?_
      simp only [Cslib.BitString.length_listRow] at hi
      rw [Cslib.BitString.getElem_listRow hi, Cslib.BitString.getElem_listRow hi, hr_bit]
    have hflat : Cslib.BitString.listRow L v w = Cslib.BitString.binaryWord L (t v) := by
      have := Cslib.BitString.listRow_flatMap_append (fun v => Cslib.BitString.binaryWord L (t v))
        (List.range B) (fun u _ => Cslib.BitString.length_binaryWord (ht_lt u)) [] v
        (by simpa using hv)
      simpa only [List.append_nil, List.getElem_range] using this
    rw [thresholdOf, hrow, hflat, Cslib.BitString.boundedBinaryValue_eq,
      Cslib.BitString.binaryValue_binaryWord, Nat.min_eq_right (ht_le v)]
  refine ⟨r, hr_lt, fun j => ?_⟩
  unfold bucketOf
  have hcongr : (List.range (B - 1)).countP (fun v => decide (thresholdOf n L r v ≤ j.val)) =
      (List.range (B - 1)).countP (fun v => decide (v < (β j).val)) := by
    refine List.countP_congr fun v hv => ?_
    have hvB : v < B := by
      rw [List.mem_range] at hv
      omega
    rw [hthresh v hvB]
    simp [ht_iff j v]
  exact hcongr.trans (countP_range_lt (m := B - 1) (k := (β j).val) (by have := (β j).isLt; omega))

/-- Packing a vertex coloring $f : \mathrm{Fin}\, N \to \mathrm{Fin}\, 3$ into block assignment
numbers below $\mathrm{numAssignments}\, N$. -/
private theorem exists_block_assignments_of_coloring {N : ℕ} (f : Fin N → Fin 3) :
    ∃ a : Fin (numBlocks N) → Fin (numAssignments N),
      (∀ i : Fin (numBlocks N), validAssignment (blockSize N) (a i).val = true) ∧
      ∀ p : Fin N,
        extractColor (a ⟨p.val / blockSize N, div_blockSize_lt_numBlocks p.isLt⟩).val
          (p.val % blockSize N) = (f p).val := by
  set b := blockSize N
  set B := numAssignments N
  set n := numBlocks N
  let col (i u : ℕ) : ℕ :=
    if h : i * b + u < N then (f ⟨i * b + u, h⟩).val else 0
  have hcol_lt (i u : ℕ) : col i u < 3 := by
    dsimp only [col]
    split_ifs with h
    · exact (f ⟨i * b + u, h⟩).isLt
    · decide
  let bitFn (i idx : ℕ) : Bool :=
    let u := idx / 2
    if idx % 2 = 0 then decide (col i u % 2 = 1) else decide (col i u / 2 = 1)
  let word (i : ℕ) : List Bool := (List.range (2 * b)).map (bitFn i)
  let a (i : Fin n) : Fin B :=
    ⟨(BitVec.ofBoolListLE (word i.val)).toNat, by
      simpa only [word, List.length_map, List.length_range, B, numAssignments] using
        (BitVec.isLt (BitVec.ofBoolListLE (word i.val)))⟩
  have hextract (i : Fin n) (u : ℕ) (hu : u < b) : extractColor (a i).val u = col i.val u := by
    have h0 : (a i).val.testBit (2 * u) = decide (col i.val u % 2 = 1) := by
      rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp only [word, List.length_map, List.length_range]; omega)]
      simp [word, bitFn, Nat.mul_div_right _ two_pos]
    have h1 : (a i).val.testBit (2 * u + 1) = decide (col i.val u / 2 = 1) := by
      rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp only [word, List.length_map, List.length_range]; omega)]
      have hdiv : (2 * u + 1) / 2 = u := by omega
      have hmod : (2 * u + 1) % 2 = 1 := by omega
      simp [word, bitFn, hdiv, hmod]
    rw [extractColor, h0, h1]
    have hc := hcol_lt i.val u
    rcases hcol : col i.val u with _ | _ | _ | m
    · rfl
    · rfl
    · rfl
    · omega
  refine ⟨a, fun i => ?_, fun p => ?_⟩
  · simp only [validAssignment, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    intro u hu
    rw [hextract i u hu]
    exact hcol_lt i.val u
  · have hu : p.val % b < b := Nat.mod_lt _ (blockSize_pos N)
    rw [hextract _ (p.val % b) hu]
    have hp_eq : p.val / b * b + p.val % b = p.val := by
      have := Nat.div_add_mod p.val b
      nlinarith
    change (if h : p.val / b * b + p.val % b < N then
      (f ⟨p.val / b * b + p.val % b, h⟩).val else 0) = (f p).val
    simp only [hp_eq, p.isLt, ↓reduceDIte, Fin.eta]

/-- **Equivalence of `ThreeColoring` and the `bpisOfColoring` search**: a graph $H$ is 3-colorable
if and only if some $r < 2^{\mathrm{searchBits}\, |V|}$ yields a satisfiable instance
`bpisOfColoring (H, r)`. -/
theorem mem_ThreeColoring_iff_exists_bpisOfColoring (H : Graph) :
    H ∈ ThreeColoring ↔
      ∃ r < 2 ^ searchBits H.1.length,
        bpisOfColoring (H, r) ∈ BipartitePermutationIndependentSet := by
  set N := H.1.length
  set b := blockSize N
  set B := numAssignments N
  set n := numBlocks N
  set L := wordLen N
  rw [mem_ThreeColoring_iff_fin]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨a, ha_valid, ha_col⟩ := exists_block_assignments_of_coloring f
    obtain ⟨r, hr_lt, hr_bucket⟩ := exists_bucketOf_eq_sort N a
    let σ : Equiv.Perm (Fin n) := Tuple.sort a
    let π : Equiv.Perm (Fin n) := σ.symm
    have hbucket_pi (i : Fin n) : bucketOf B n L r (π i).val = (a i).val := by
      rw [hr_bucket (π i)]
      simp [π, σ]
    refine ⟨r, hr_lt, π, π, fun e he hu₁ hu₂ hv₁ hv₂ h1 h2 => ?_⟩
    simp only [bpisOfColoring, List.mem_append] at he
    rcases he with (he | he) | he
    · -- consistencyEdges
      simp only [consistencyEdges, List.mem_flatMap, List.mem_range, List.mem_map,
        List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at he
      obtain ⟨i, _hi, j₁, _hj₁, j₂, ⟨_hj₂, hne⟩, rfl⟩ := he
      have h1' : (π ⟨i, hu₁⟩).val = j₁ := congrArg Fin.val h1
      have h2' : (π ⟨i, hv₁⟩).val = j₂ := congrArg Fin.val h2
      exact hne (h1'.symm.trans h2')
    · -- invalidBucketEdges
      simp only [invalidBucketEdges, List.mem_flatMap, List.mem_range, List.mem_map,
        List.mem_filter, Bool.not_eq_true'] at he
      obtain ⟨i, _hi, j, ⟨_hj, hinv⟩, rfl⟩ := he
      have h1' : (π ⟨i, hu₁⟩).val = j := congrArg Fin.val h1
      rw [← h1', hbucket_pi ⟨i, hu₁⟩] at hinv
      have hval := ha_valid ⟨i, hu₁⟩
      exact Bool.false_ne_true (hinv.symm.trans hval)
    · -- conflictEdges
      simp only [conflictEdges, vertexConflictEdges, pairConflictEdges, innerConflictEdges,
        innerConflictBuckets, innerConflictTest,
        List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
        Bool.and_eq_true, decide_eq_true_eq] at he
      obtain ⟨p, hp, q, ⟨hq, hadj⟩, j₁, _hj₁, j₂, ⟨_hj₂, _, hcol_eq⟩, rfl⟩ := he
      dsimp only at hu₁ hv₁ h1 h2
      have h1' : (π ⟨p / b, hu₁⟩).val = j₁ := congrArg Fin.val h1
      have h2' : (π ⟨q / b, hv₁⟩).val = j₂ := congrArg Fin.val h2
      unfold colorAt at hcol_eq
      change extractColor (bucketOf B n L r j₁) (p % b) =
        extractColor (bucketOf B n L r j₂) (q % b) at hcol_eq
      rw [← h1', hbucket_pi ⟨p / b, hu₁⟩, ← h2', hbucket_pi ⟨q / b, hv₁⟩] at hcol_eq
      have hp_col := ha_col ⟨p, hp⟩
      have hq_col := ha_col ⟨q, hq⟩
      rw [hp_col, hq_col] at hcol_eq
      rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hq] at hadj
      exact hf ⟨p, hp⟩ ⟨q, hq⟩ hadj (Fin.ext hcol_eq)
  · rintro ⟨r, _, π₁, π₂, hG⟩
    change Equiv.Perm (Fin n) at π₁ π₂
    have hπ_eq (i : Fin n) : π₁ i = π₂ i := by
      by_contra hne
      have hne_val : (π₁ i).val ≠ (π₂ i).val := mt Fin.ext hne
      have he : ((i.val, (π₁ i).val), (i.val, (π₂ i).val)) ∈
          (bpisOfColoring (H, r)).2 := by
        simp only [bpisOfColoring, List.mem_append]
        left; left
        simp only [consistencyEdges, List.mem_flatMap, List.mem_range, List.mem_map,
          List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
        exact ⟨i.val, i.isLt, (π₁ i).val, (π₁ i).isLt, (π₂ i).val,
          ⟨(π₂ i).isLt, hne_val⟩, rfl⟩
      exact hG _ he i.isLt (π₁ i).isLt i.isLt (π₂ i).isLt rfl rfl
    have hvalid (i : Fin n) :
        validAssignment b (bucketOf B n L r (π₁ i).val) = true := by
      by_contra hinv
      rw [Bool.not_eq_true] at hinv
      have he : ((i.val, (π₁ i).val), (i.val, (π₁ i).val)) ∈
          (bpisOfColoring (H, r)).2 := by
        simp only [bpisOfColoring, List.mem_append]
        left; right
        simp only [invalidBucketEdges, List.mem_flatMap, List.mem_range, List.mem_map,
          List.mem_filter, Bool.not_eq_true']
        exact ⟨i.val, i.isLt, (π₁ i).val, ⟨(π₁ i).isLt, hinv⟩, rfl⟩
      exact hG _ he i.isLt (π₁ i).isLt i.isLt (π₁ i).isLt rfl (hπ_eq i).symm
    let c (p : Fin N) : ℕ :=
      extractColor (bucketOf B n L r (π₁ ⟨p.val / b, div_blockSize_lt_numBlocks p.isLt⟩).val)
        (p.val % b)
    have hc_lt (p : Fin N) : c p < 3 := by
      have hv := hvalid ⟨p.val / b, div_blockSize_lt_numBlocks p.isLt⟩
      simp only [validAssignment, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hv
      exact hv (p.val % b) (Nat.mod_lt _ (blockSize_pos N))
    refine ⟨fun p => ⟨c p, hc_lt p⟩, fun p q hadj hfeq => ?_⟩
    have hceq : c p = c q := congrArg Fin.val hfeq
    set i₁ : Fin n := ⟨p.val / b, div_blockSize_lt_numBlocks p.isLt⟩
    set i₂ : Fin n := ⟨q.val / b, div_blockSize_lt_numBlocks q.isLt⟩
    have he : ((i₁.val, (π₁ i₁).val), (i₂.val, (π₁ i₂).val)) ∈
        (bpisOfColoring (H, r)).2 := by
      simp only [bpisOfColoring, List.mem_append]
      right
      simp only [conflictEdges, vertexConflictEdges, pairConflictEdges, innerConflictEdges,
        innerConflictBuckets, innerConflictTest,
        List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
        Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        decide_eq_true_eq]
      refine ⟨p.val, p.isLt, q.val, ⟨q.isLt, ?_⟩, (π₁ i₁).val, (π₁ i₁).isLt,
        (π₁ i₂).val, ⟨(π₁ i₂).isLt, ?_, hceq⟩, rfl⟩
      · rw [List.getD_eq_getElem _ _ p.isLt, List.getD_eq_getElem _ _ q.isLt]
        exact hadj
      · by_cases hi : i₁.val = i₂.val
        · right; exact congrArg (fun k : Fin n => (π₁ k).val) (Fin.ext hi)
        · left; exact hi
    exact hG _ he i₁.isLt (π₁ i₁).isLt i₂.isLt (π₁ i₂).isLt rfl (hπ_eq i₂).symm

/-! ### Polynomial-time computability of the reduction -/

@[local fun_prop]
private theorem computableInPolyTime_unary_log_two :
    ComputableInPolyTime (Nat.log 2) encUnary encUnary :=
  binary_log_two.comp unary_to_binary

@[local fun_prop]
private theorem computableInPolyTime_bool_toUnary :
    ComputableInPolyTime Bool.toNat encBool encUnary :=
  of_finite _

@[local fun_prop]
private theorem computableInPolyTime_nat_bits :
    ComputableInPolyTime Nat.bits encNat encBits :=
  of_eq fun _ => rfl

@[local fun_prop]
private theorem computableInPolyTime_unary_div'
    {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → ℕ}
    (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => a x / b x) encIn encUnary :=
  unary_div.comp (ha.prod hb)

@[local fun_prop]
private theorem computableInPolyTime_unary_mod'
    {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → ℕ}
    (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => a x % b x) encIn encUnary :=
  unary_mod.comp (ha.prod hb)

@[local fun_prop]
private theorem computableInPolyTime_blockSize :
    ComputableInPolyTime blockSize encUnary encUnary := by
  unfold blockSize
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_numAssignments :
    ComputableInPolyTime numAssignments encUnary encUnary := by
  obtain ⟨hefficient, hspec⟩ := iterate_spec (count := fun n => 2 * blockSize n)
    (init := fun _ => 1) (step := fun state => state * 2)
    (encIn := encUnary) (encState := encUnary)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun _ i state => state = 2 ^ i) (fun _ => rfl)
    (fun _ _ _ _ h => by rw [h, pow_succ])
    (size := fun n => 4 * n + 4) (polyBounded (by fun_prop)) (fun n i state hi h => by
      simp only [encUnary_apply, List.length_replicate, h]
      exact (Nat.pow_le_pow_right two_pos hi).trans (numAssignments_le n))
  convert hefficient using 1
  funext n
  exact (hspec n).symm

@[local fun_prop]
private theorem computableInPolyTime_numBlocks :
    ComputableInPolyTime numBlocks encUnary encUnary := by
  unfold numBlocks
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_wordLen :
    ComputableInPolyTime wordLen encUnary encUnary := by
  unfold wordLen
  fun_prop

/-- Computing `searchBits` is polynomial-time in the plain machine model. -/
@[fun_prop]
theorem computableInPolyTime_searchBits :
    ComputableInPolyTime searchBits encUnary encUnary := by
  unfold searchBits
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_extractColor
    {γ : Type} {encIn : γ ↪ List Bool} {c u : γ → ℕ}
    (hc : ComputableInPolyTime c encIn encUnary)
    (_hu : ComputableInPolyTime u encIn encUnary) :
    ComputableInPolyTime (fun x => extractColor (c x) (u x)) encIn encUnary := by
  have hc_bin : ComputableInPolyTime c encIn encNat := unary_to_binary.comp hc
  unfold extractColor
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_validAssignment
    {γ : Type} {encIn : γ ↪ List Bool} {b c : γ → ℕ}
    (_hb : ComputableInPolyTime b encIn encUnary)
    (_hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => validAssignment (b x) (c x)) encIn encBool := by
  unfold validAssignment
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_thresholdOf
    {γ : Type} {encIn : γ ↪ List Bool} {n L r v : γ → ℕ}
    (_hn : ComputableInPolyTime n encIn encUnary)
    (_hL : ComputableInPolyTime L encIn encUnary)
    (_hr : ComputableInPolyTime r encIn encNat)
    (_hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime (fun x => thresholdOf (n x) (L x) (r x) (v x)) encIn encUnary := by
  unfold thresholdOf
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_bucketOf
    {γ : Type} {encIn : γ ↪ List Bool} {B n L r j : γ → ℕ}
    (_hB : ComputableInPolyTime B encIn encUnary)
    (_hn : ComputableInPolyTime n encIn encUnary)
    (_hL : ComputableInPolyTime L encIn encUnary)
    (_hr : ComputableInPolyTime r encIn encNat)
    (_hj : ComputableInPolyTime j encIn encUnary) :
    ComputableInPolyTime (fun x => bucketOf (B x) (n x) (L x) (r x) (j x))
      encIn encUnary := by
  unfold bucketOf
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_colorAt
    {γ : Type} {encIn : γ ↪ List Bool} {N r j u : γ → ℕ}
    (_hN : ComputableInPolyTime N encIn encUnary)
    (_hr : ComputableInPolyTime r encIn encNat)
    (_hj : ComputableInPolyTime j encIn encUnary)
    (_hu : ComputableInPolyTime u encIn encUnary) :
    ComputableInPolyTime (fun x => colorAt (N x) (r x) (j x) (u x)) encIn encUnary := by
  unfold colorAt
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_consistencyEdges :
    ComputableInPolyTime consistencyEdges encUnary
      (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  unfold consistencyEdges
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_invalidBucketEdges :
    ComputableInPolyTime (fun p : ℕ × ℕ => invalidBucketEdges p.1 p.2)
      (encPair encUnary encNat)
      (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  unfold invalidBucketEdges
  fun_prop

private theorem computableInPolyTime_bool_or'
    {α : Type} {encA : α ↪ List Bool} {left right : α → Bool}
    (hleft : ComputableInPolyTime left encA encBool)
    (hright : ComputableInPolyTime right encA encBool) :
    ComputableInPolyTime (fun a => left a || right a) encA encBool :=
  bool_or.comp (hleft.prod hright)

@[local fun_prop]
private theorem computableInPolyTime_innerConflictTest
    {γ : Type} {encIn : γ ↪ List Bool} {N r p q j₁ j₂ : γ → ℕ}
    (_hN : ComputableInPolyTime N encIn encUnary)
    (_hr : ComputableInPolyTime r encIn encNat)
    (_hp : ComputableInPolyTime p encIn encUnary)
    (_hq : ComputableInPolyTime q encIn encUnary)
    (_hj₁ : ComputableInPolyTime j₁ encIn encUnary)
    (_hj₂ : ComputableInPolyTime j₂ encIn encUnary) :
    ComputableInPolyTime
      (fun x => innerConflictTest (N x) (r x) (p x) (q x) (j₁ x) (j₂ x))
      encIn encBool := by
  unfold innerConflictTest
  exact bool_and' (computableInPolyTime_bool_or' (by fun_prop) (by fun_prop)) (by fun_prop)

@[local fun_prop]
private theorem computableInPolyTime_innerConflictBuckets
    {γ : Type} {encIn : γ ↪ List Bool} {N r p q j₁ : γ → ℕ}
    (_hN : ComputableInPolyTime N encIn encUnary)
    (_hr : ComputableInPolyTime r encIn encNat)
    (_hp : ComputableInPolyTime p encIn encUnary)
    (_hq : ComputableInPolyTime q encIn encUnary)
    (_hj₁ : ComputableInPolyTime j₁ encIn encUnary) :
    ComputableInPolyTime
      (fun x => innerConflictBuckets (N x) (r x) (p x) (q x) (j₁ x))
      encIn (encList encUnary) := by
  unfold innerConflictBuckets
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_innerConflictEdges
    {γ : Type} {encIn : γ ↪ List Bool} {N r p q j₁ : γ → ℕ}
    (_hN : ComputableInPolyTime N encIn encUnary)
    (_hr : ComputableInPolyTime r encIn encNat)
    (_hp : ComputableInPolyTime p encIn encUnary)
    (_hq : ComputableInPolyTime q encIn encUnary)
    (_hj₁ : ComputableInPolyTime j₁ encIn encUnary) :
    ComputableInPolyTime
      (fun x => innerConflictEdges (N x) (r x) (p x) (q x) (j₁ x))
      encIn (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  unfold innerConflictEdges
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_pairConflictEdges
    {γ : Type} {encIn : γ ↪ List Bool} {N r p q : γ → ℕ}
    (_hN : ComputableInPolyTime N encIn encUnary)
    (_hr : ComputableInPolyTime r encIn encNat)
    (_hp : ComputableInPolyTime p encIn encUnary)
    (_hq : ComputableInPolyTime q encIn encUnary) :
    ComputableInPolyTime
      (fun x => pairConflictEdges (N x) (r x) (p x) (q x))
      encIn (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  unfold pairConflictEdges
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_vertexConflictEdges
    {γ : Type} {encIn : γ ↪ List Bool} {H : γ → Graph} {r p : γ → ℕ}
    (hH : ComputableInPolyTime H encIn encGraph)
    (_hr : ComputableInPolyTime r encIn encNat)
    (_hp : ComputableInPolyTime p encIn encUnary) :
    ComputableInPolyTime
      (fun x => vertexConflictEdges (H x) (r x) (p x))
      encIn (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  have hverts : ComputableInPolyTime (fun x => (H x).1) encIn (encList encNat) :=
    (fst (encList encNat) (encList (encPair encNat encNat))).comp hH
  have hlen : ComputableInPolyTime (fun x => (H x).1.length) encIn encUnary :=
    (length_list encNat).comp hverts
  unfold vertexConflictEdges
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_conflictEdges :
    ComputableInPolyTime (fun p : Graph × ℕ => conflictEdges p.1 p.2)
      (encPair encGraph encNat)
      (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  have hH : ComputableInPolyTime (fun p : Graph × ℕ => p.1)
      (encPair encGraph encNat) encGraph := fst encGraph encNat
  have hverts : ComputableInPolyTime (fun p : Graph × ℕ => p.1.1)
      (encPair encGraph encNat) (encList encNat) :=
    (fst (encList encNat) (encList (encPair encNat encNat))).comp hH
  have hlen : ComputableInPolyTime (fun p : Graph × ℕ => p.1.1.length)
      (encPair encGraph encNat) encUnary := (length_list encNat).comp hverts
  unfold conflictEdges
  fun_prop

/-- Constructing `bpisOfColoring (H, r)` is polynomial-time in the plain machine model. -/
@[fun_prop]
theorem computableInPolyTime_bpisOfColoring :
    ComputableInPolyTime bpisOfColoring (encPair encGraph encNat)
      encBipartitePermutationGraph := by
  have hH : ComputableInPolyTime (fun p : Graph × ℕ => p.1)
      (encPair encGraph encNat) encGraph := fst encGraph encNat
  have hverts : ComputableInPolyTime (fun p : Graph × ℕ => p.1.1)
      (encPair encGraph encNat) (encList encNat) :=
    (fst (encList encNat) (encList (encPair encNat encNat))).comp hH
  have hlen : ComputableInPolyTime (fun x : Graph × ℕ => x.1.1.length)
      (encPair encGraph encNat) encUnary := (length_list encNat).comp hverts
  unfold bpisOfColoring encBipartitePermutationGraph
  fun_prop

/-- Converting a `BipartitePermutationGraph` from unary to binary coordinate encoding is
polynomial-time in the plain machine model. -/
@[fun_prop]
theorem computableInPolyTime_toBinary :
    ComputableInPolyTime id encBipartitePermutationGraph
      encBipartitePermutationGraphBinary := by
  have heq : (id : BipartitePermutationGraph → BipartitePermutationGraph) =
      fun G => (G.1, G.2.map fun e => ((e.1.1, e.1.2), (e.2.1, e.2.2))) := by
    funext ⟨n, E⟩
    simp
  rw [heq]
  unfold encBipartitePermutationGraph encBipartitePermutationGraphBinary
  fun_prop

/-- Constructing `bpisOfColoring (H, r)` under binary coordinate encoding is polynomial-time in the
plain machine model. -/
@[fun_prop]
theorem computableInPolyTime_bpisOfColoring_binary :
    ComputableInPolyTime bpisOfColoring (encPair encGraph encNat)
      encBipartitePermutationGraphBinary :=
  computableInPolyTime_toBinary.comp computableInPolyTime_bpisOfColoring

/-- Computing `searchBits H.1.length` from a graph `H` is polynomial-time in the plain machine
model. -/
@[fun_prop]
theorem computableInPolyTime_searchBits_length :
    ComputableInPolyTime (fun H : Graph => searchBits H.1.length) encGraph encUnary := by
  refine computableInPolyTime_searchBits.comp ?_
  unfold encGraph
  fun_prop

/-! ### Exhaustive search over threshold tables and the ETH lower bound -/

/-- **Transfer of exponential-time deciders along the block-sorting reduction**: for every
$M \ge 1$ and $\delta \ge 0$, a decider for `BipartitePermutationIndependentSet` within time
$2^{\delta n \log_2 n} \cdot \mathrm{poly}(|G|)$ yields a decider for `ThreeColoring` within time
$2^{(1 / M + 10 \delta) |V|} \cdot \mathrm{poly}(|H|)$. -/
theorem decidableInExpTime_ThreeColoring_of_bpis {M : ℕ} (hM : 0 < M) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime BipartitePermutationIndependentSet encBipartitePermutationGraph
      (fun G => G.1 * Nat.log 2 G.1) δ) :
    DecidableInExpTime ThreeColoring encGraph (fun H => H.1.length) (1 / M + 10 * δ) := by
  simpa using h.of_exhaustiveSearch computableInPolyTime_bpisOfColoring
    computableInPolyTime_searchBits_length mem_ThreeColoring_iff_exists_bpisOfColoring (c := 10)
    (fun H r => by have := fst_bpisOfColoring_mul_log_le H r; omega)
    (fun H => searchBits_le_div_add H.1.length hM) hδ

end BipartitePermutationIndependentSet

open BipartitePermutationIndependentSet in
/-- **Subexponential-time transfer from `BipartitePermutationIndependentSet` to `ThreeColoring`**:
if `BipartitePermutationIndependentSet` is decidable in time $2^{o(n \log n)}$, then
`ThreeColoring` is decidable in time $2^{o(|V|)}$. -/
theorem DecidableInSubexpTime.threeColoring_of_bipartitePermutationIndependentSet
    (h : DecidableInSubexpTime BipartitePermutationIndependentSet encBipartitePermutationGraph
      fun G => G.1 * Nat.log 2 G.1) :
    DecidableInSubexpTime ThreeColoring encGraph fun H => H.1.length :=
  h.of_exhaustiveSearch computableInPolyTime_bpisOfColoring computableInPolyTime_searchBits_length
    mem_ThreeColoring_iff_exists_bpisOfColoring (c := 10)
    (fun H r => by have := fst_bpisOfColoring_mul_log_le H r; omega)
    (fun M hM => ⟨48 * (48 * M) ^ 3, fun H => searchBits_le_div_add H.1.length hM⟩)

/-- **Lokshtanov–Marx–Saurabh ETH Lower Bound for $2n \times 2n$ Bipartite Permutation Independent
Set** [LokshtanovMarxSaurabh2018, Theorem 2.11] [Ilango2020FOCS, Section III.B, p. 427; ECCC
TR20-183, Section 3, Theorem 10, p. 20]: under `ETH`,
`BipartitePermutationIndependentSet` is not decidable within time $2^{o(n \log n)}$, i.e., for some
$\delta > 0$, no algorithm decides `BipartitePermutationIndependentSet` within time
$2^{\delta n \log_2 n}$ times a polynomial in the length of the encoded instance. -/
theorem ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet (h : ETH) :
    ¬DecidableInSubexpTime BipartitePermutationIndependentSet encBipartitePermutationGraph
      fun G => G.1 * Nat.log 2 G.1 :=
  fun hsub => h.not_decidableInSubexpTime_ThreeColoring_vertices
    hsub.threeColoring_of_bipartitePermutationIndependentSet

/-- **Binary-encoded variant of the Lokshtanov–Marx–Saurabh ETH lower bound**
[LokshtanovMarxSaurabh2018, Theorem 2.11] [Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183,
Section 3, Theorem 10, p. 20]: under `ETH`,
`BipartitePermutationIndependentSet` is not decidable in time $2^{o(n \log n)}$ under binary
coordinate encoding. -/
theorem ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet_binary (h : ETH) :
    ¬DecidableInSubexpTime BipartitePermutationIndependentSet encBipartitePermutationGraphBinary
      fun G => G.1 * Nat.log 2 G.1 := by
  intro hsub
  refine h.not_decidableInSubexpTime_BipartitePermutationIndependentSet ?_
  exact hsub.of_reduction BipartitePermutationIndependentSet.computableInPolyTime_toBinary
    (fun _ => Iff.rfl) (c := 1) fun G => by dsimp only [id]; omega

/-- **Ceiling-logarithm variant of the Lokshtanov–Marx–Saurabh ETH lower bound**
[LokshtanovMarxSaurabh2018, Theorem 2.11] [Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183,
Section 3, Theorem 10, p. 20]: under `ETH`,
`BipartitePermutationIndependentSet` is not decidable in time $2^{o(n \lceil \log_2 n \rceil)}$. -/
theorem ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet_clog (h : ETH) :
    ¬DecidableInSubexpTime BipartitePermutationIndependentSet encBipartitePermutationGraph
      fun G => G.1 * Nat.clog 2 G.1 := by
  intro hsub
  refine h.not_decidableInSubexpTime_BipartitePermutationIndependentSet ?_
  refine hsub.mono_measure (c := 2) fun G => ?_
  rcases le_or_gt G.1 1 with hG | hG
  · have : Nat.clog 2 G.1 = 0 := Nat.clog_of_right_le_one hG 2
    simp [this]
  · have hclog : Nat.clog 2 G.1 ≤ 2 * Nat.log 2 G.1 := by
      have h1 : Nat.clog 2 G.1 ≤ Nat.log 2 G.1 + 1 := by
        rw [Nat.clog_le_iff_le_pow Nat.one_lt_two]
        exact (Nat.lt_pow_succ_log_self Nat.one_lt_two G.1).le
      have h2 : 1 ≤ Nat.log 2 G.1 := Nat.log_pos Nat.one_lt_two hG
      omega
    calc G.1 * Nat.clog 2 G.1 ≤ G.1 * (2 * Nat.log 2 G.1) := Nat.mul_le_mul_left G.1 hclog
      _ ≤ 2 * (G.1 * Nat.log 2 G.1) + 2 := by ring_nf; omega

/-- **$2n \log_2(2n)$-parameterized variant of the Lokshtanov–Marx–Saurabh ETH lower bound**
[LokshtanovMarxSaurabh2018, Theorem 2.11]: under `ETH`, `BipartitePermutationIndependentSet` is not
decidable in time $2^{o(k \log k)}$ where $k = 2n$. -/
theorem ETH.not_decidableInSubexpTime_BipartitePermutationIndependentSet_two_mul (h : ETH) :
    ¬DecidableInSubexpTime BipartitePermutationIndependentSet encBipartitePermutationGraph
      fun G => (2 * G.1) * Nat.log 2 (2 * G.1) := by
  intro hsub
  refine h.not_decidableInSubexpTime_BipartitePermutationIndependentSet ?_
  refine hsub.mono_measure (c := 4) fun G => ?_
  rcases le_or_gt G.1 1 with hG | hG
  · interval_cases G.1 <;> decide
  · have hlog : Nat.log 2 (2 * G.1) ≤ 2 * Nat.log 2 G.1 := by
      have h1 : Nat.log 2 (2 * G.1) = Nat.log 2 G.1 + 1 := by
        rw [Nat.mul_comm, Nat.log_mul_base Nat.one_lt_two (by omega)]
      have h2 : 1 ≤ Nat.log 2 G.1 := Nat.log_pos Nat.one_lt_two hG
      omega
    calc (2 * G.1) * Nat.log 2 (2 * G.1)
        ≤ (2 * G.1) * (2 * Nat.log 2 G.1) := Nat.mul_le_mul_left _ hlog
      _ ≤ 4 * (G.1 * Nat.log 2 G.1) + 4 := by ring_nf; omega

end
end Cslib.Complexity
