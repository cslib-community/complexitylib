/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.GraphProblems
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Binary
public import Mathlib.Data.Fin.Tuple.Sort
import Complexity.Computability.Complexity.FineGrained.Assignment
import Complexity.Computability.Complexity.FineGrained.BruteForce
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
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
$n \log_2 n \le 10 N + 5$ (`numBlocks_mul_log_le`), using a library proof based on monotone
threshold enumeration (`Tuple.sort` and `Tuple.lt_card_le_iff_apply_le_of_monotone`):

* Partition the $N$ vertices into $n = \lfloor N / b \rfloor + 1$ blocks of size
  $b = \lfloor (\log_2 N) / 4 \rfloor + 1$, so that $n \log_2 n \le 10 N + 5$
  (`numBlocks_mul_log_le`).
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

## Main results

* `Cslib.Complexity.BipartitePermutationGraph.exists_satisfies_iff_exists_satisfiesUndirected`,
  `Cslib.Complexity.BipartitePermutationIndependentSet.mem_iff_exists_satisfiesUndirected`:
  equivalence of Ilango's and Lokshtanov–Marx–Saurabh's formulations.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_ThreeColoring_vertices`: under `ETH`,
  `ThreeColoring` is not decidable in time $2^{o(|V|)}$.
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

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime

/-! ### Problem definitions and equivalence of formulations -/

/-- An instance of `$2n \times 2n$ Bipartite Permutation Independent Set`
[Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183, Section 3, Theorem 10, p. 20]: a parameter
$n$ together with a list of directed edges $((u_1, u_2), (v_1, v_2))$ between vertex pairs in
$[n] \times [n]$. -/
abbrev BipartitePermutationGraph : Type := ℕ × List ((ℕ × ℕ) × (ℕ × ℕ))

/-- Unary encoding of a `BipartitePermutationGraph`, matching Ilango's presentation in which the
graph has $O(n^2)$ vertices and coordinates are bounded by $n$
[Ilango2020FOCS, Section III.B, p. 427; ECCC TR20-183, Section 3, p. 20]. -/
def encBipartitePermutationGraph : BipartitePermutationGraph ↪ List Bool :=
  encPair encUnary (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary)))

/-- Binary encoding of a `BipartitePermutationGraph`. -/
def encBipartitePermutationGraphBinary : BipartitePermutationGraph ↪ List Bool :=
  encPair encNat (encList (encPair (encPair encNat encNat) (encPair encNat encNat)))

namespace BipartitePermutationGraph

/-- **Ilango's directed satisfaction predicate** [Ilango2020FOCS, Section III.B, p. 427; ECCC
TR20-183, Section 3, Theorem 10, p. 20]: two permutations $\pi_1, \pi_2 \in S_n$ satisfy $G$ when
for no edge $((u_1, u_2), (v_1, v_2)) \in G.2$ with coordinates below $n = G.1$ do we have both
$\pi_1(u_1) = u_2$ and $\pi_2(v_1) = v_2$. -/
def Satisfies (G : BipartitePermutationGraph) (π₁ π₂ : Equiv.Perm (Fin G.1)) : Prop :=
  ∀ e ∈ G.2, ∀ (hu₁ : e.1.1 < G.1) (hu₂ : e.1.2 < G.1) (hv₁ : e.2.1 < G.1) (hv₂ : e.2.2 < G.1),
    π₁ ⟨e.1.1, hu₁⟩ = ⟨e.1.2, hu₂⟩ → π₂ ⟨e.2.1, hv₁⟩ ≠ ⟨e.2.2, hv₂⟩

/-- A permutation of $\mathrm{Fin}\,(2n)$ is **block-preserving** when it maps the first half
$[0, n)$ to $[0, n)$ (and hence the second half $[n, 2n)$ to $[n, 2n)$)
[LokshtanovMarxSaurabh2018, Theorem 2.11]. -/
def IsBlockPreserving {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) : Prop :=
  ∀ i : Fin (2 * n), i.val < n ↔ (π i).val < n

/-- **Lokshtanov–Marx–Saurabh's undirected bipartite satisfaction predicate**
[LokshtanovMarxSaurabh2018, Section 2.2, Theorem 2.11]: a single permutation
$\pi \in S_{2n}$ preserves the two blocks $[0, n)$ and $[n, 2n)$ and for no conflict edge
$((u_1, u_2), (v_1, v_2)) \in G.2$ between the two blocks do we have both $\pi(u_1) = u_2$ and
$\pi(n + v_1) = n + v_2$. -/
def SatisfiesUndirected (G : BipartitePermutationGraph) (π : Equiv.Perm (Fin (2 * G.1))) : Prop :=
  IsBlockPreserving π ∧
    ∀ e ∈ G.2, ∀ (hu₁ : e.1.1 < G.1) (_hu₂ : e.1.2 < G.1) (hv₁ : e.2.1 < G.1) (_hv₂ : e.2.2 < G.1),
      (π ⟨e.1.1, by omega⟩).val = e.1.2 → (π ⟨G.1 + e.2.1, by omega⟩).val ≠ G.1 + e.2.2

theorem IsBlockPreserving.symm {n : ℕ} {π : Equiv.Perm (Fin (2 * n))}
    (hπ : IsBlockPreserving π) : IsBlockPreserving π.symm := by
  intro i
  simpa only [π.apply_symm_apply] using (hπ (π.symm i)).symm

/-- Combining two permutations $\pi_1, \pi_2 \in S_n$ on the two halves of $\mathrm{Fin}\,(2n)$. -/
def combinePerm {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (2 * n)) where
  toFun i :=
    if h : i.val < n then
      ⟨(π₁ ⟨i.val, h⟩).val, by have := (π₁ ⟨i.val, h⟩).isLt; omega⟩
    else
      ⟨n + (π₂ ⟨i.val - n, by omega⟩).val, by have := (π₂ ⟨i.val - n, by omega⟩).isLt; omega⟩
  invFun i :=
    if h : i.val < n then
      ⟨(π₁.symm ⟨i.val, h⟩).val, by have := (π₁.symm ⟨i.val, h⟩).isLt; omega⟩
    else
      ⟨n + (π₂.symm ⟨i.val - n, by omega⟩).val,
        by have := (π₂.symm ⟨i.val - n, by omega⟩).isLt; omega⟩
  left_inv i := by
    ext
    dsimp only
    split_ifs with h₁ h₂ h₃
    · simp [Fin.eta]
    · exfalso
      dsimp only at h₂
      exact h₂ (π₁ ⟨i.val, h₁⟩).isLt
    · exfalso
      dsimp only at h₃
      omega
    · have hsub : n + (π₂ ⟨i.val - n, by omega⟩).val - n = (π₂ ⟨i.val - n, by omega⟩).val := by
        omega
      simp only [hsub, Fin.eta, Equiv.symm_apply_apply]
      omega
  right_inv i := by
    ext
    dsimp only
    split_ifs with h₁ h₂ h₃
    · simp [Fin.eta]
    · exfalso
      dsimp only at h₂
      exact h₂ (π₁.symm ⟨i.val, h₁⟩).isLt
    · exfalso
      dsimp only at h₃
      omega
    · have hsub : n + (π₂.symm ⟨i.val - n, by omega⟩).val - n =
          (π₂.symm ⟨i.val - n, by omega⟩).val := by
        omega
      simp only [hsub, Fin.eta, Equiv.apply_symm_apply]
      omega

theorem isBlockPreserving_combinePerm {n : ℕ} (π₁ π₂ : Equiv.Perm (Fin n)) :
    IsBlockPreserving (combinePerm π₁ π₂) := by
  intro i
  simp only [combinePerm, Equiv.coe_fn_mk]
  split_ifs with h
  · have := (π₁ ⟨i.val, h⟩).isLt
    simp [h, this]
  · simp [h, show ¬n + (π₂ ⟨i.val - n, by omega⟩).val < n by omega]

/-- Extracting the first-half permutation on $\mathrm{Fin}\, n$ from a block-preserving permutation
of $\mathrm{Fin}\,(2n)$. -/
def fstPerm {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) (hπ : IsBlockPreserving π) :
    Equiv.Perm (Fin n) where
  toFun i := ⟨(π ⟨i.val, by omega⟩).val, (hπ ⟨i.val, by omega⟩).mp i.isLt⟩
  invFun i := ⟨(π.symm ⟨i.val, by omega⟩).val, (hπ.symm ⟨i.val, by omega⟩).mp i.isLt⟩
  left_inv i := by
    ext
    simp [Fin.eta]
  right_inv i := by
    ext
    simp [Fin.eta]

/-- Extracting the second-half permutation on $\mathrm{Fin}\, n$ from a block-preserving permutation
of $\mathrm{Fin}\,(2n)$. -/
def sndPerm {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) (hπ : IsBlockPreserving π) :
    Equiv.Perm (Fin n) where
  toFun i :=
    ⟨(π ⟨n + i.val, by omega⟩).val - n, by
      have h1 : ¬(⟨n + i.val, by omega⟩ : Fin (2 * n)).val < n := by simp
      have h2 := mt (hπ ⟨n + i.val, by omega⟩).mpr h1
      have h3 := (π ⟨n + i.val, by omega⟩).isLt
      omega⟩
  invFun i :=
    ⟨(π.symm ⟨n + i.val, by omega⟩).val - n, by
      have h1 : ¬(⟨n + i.val, by omega⟩ : Fin (2 * n)).val < n := by simp
      have h2 := mt (hπ.symm ⟨n + i.val, by omega⟩).mpr h1
      have h3 := (π.symm ⟨n + i.val, by omega⟩).isLt
      omega⟩
  left_inv i := by
    ext
    dsimp only
    have h1 : ¬(⟨n + i.val, by omega⟩ : Fin (2 * n)).val < n := by simp
    have h2 : n ≤ (π ⟨n + i.val, by omega⟩).val :=
      Nat.le_of_not_lt (mt (hπ ⟨n + i.val, by omega⟩).mpr h1)
    have h3 : (⟨n + ((π ⟨n + i.val, by omega⟩).val - n), by omega⟩ : Fin (2 * n)) =
        π ⟨n + i.val, by omega⟩ := by
      ext
      dsimp only
      omega
    rw [h3, π.symm_apply_apply]
    dsimp only
    omega
  right_inv i := by
    ext
    dsimp only
    have h1 : ¬(⟨n + i.val, by omega⟩ : Fin (2 * n)).val < n := by simp
    have h2 : n ≤ (π.symm ⟨n + i.val, by omega⟩).val :=
      Nat.le_of_not_lt (mt (hπ.symm ⟨n + i.val, by omega⟩).mpr h1)
    have h3 : (⟨n + ((π.symm ⟨n + i.val, by omega⟩).val - n), by omega⟩ : Fin (2 * n)) =
        π.symm ⟨n + i.val, by omega⟩ := by
      ext
      dsimp only
      omega
    rw [h3, π.apply_symm_apply]
    dsimp only
    omega

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
    simp only [combinePerm, Equiv.coe_fn_mk, hu₁, ↓reduceDIte] at h1
    have hnot : ¬G.1 + e.2.1 < G.1 := by omega
    simp only [combinePerm, Equiv.coe_fn_mk, hnot, ↓reduceDIte] at h2
    have hsub : G.1 + e.2.1 - G.1 = e.2.1 := by omega
    have hπ₁ : π₁ ⟨e.1.1, hu₁⟩ = ⟨e.1.2, hu₂⟩ := Fin.ext h1
    have hπ₂ : π₂ ⟨e.2.1, hv₁⟩ = ⟨e.2.2, hv₂⟩ := by
      ext
      have h2' : (π₂ ⟨G.1 + e.2.1 - G.1, by omega⟩).val = e.2.2 := by omega
      simpa only [hsub] using h2'
    exact hG e he hu₁ hu₂ hv₁ hv₂ hπ₁ hπ₂
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
def BipartitePermutationIndependentSet : Set BipartitePermutationGraph :=
  {G | ∃ π₁ π₂ : Equiv.Perm (Fin G.1), G.Satisfies π₁ π₂}

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
def blockSize (N : ℕ) : ℕ := Nat.log 2 N / 4 + 1

/-- Number of $2b$-bit block-coloring assignments $B = 2^{2b} = 4^b$. -/
def numAssignments (N : ℕ) : ℕ := 2 ^ (2 * blockSize N)

/-- Number of vertex blocks $n = \lfloor N / b \rfloor + 1$. -/
def numBlocks (N : ℕ) : ℕ := N / blockSize N + 1

/-- Bit-width $L = \lfloor \log_2 n \rfloor + 1$ of each threshold count in $\{0, \ldots, n\}$. -/
def wordLen (N : ℕ) : ℕ := Nat.log 2 (numBlocks N) + 1

/-- Total number of bits $K = B \cdot L$ in a threshold table. -/
def searchBits (N : ℕ) : ℕ := numAssignments N * wordLen N

theorem blockSize_pos (N : ℕ) : 0 < blockSize N := Nat.succ_pos _

theorem numBlocks_pos (N : ℕ) : 0 < numBlocks N := Nat.succ_pos _

theorem div_blockSize_lt_numBlocks {N p : ℕ} (hp : p < N) :
    p / blockSize N < numBlocks N := by
  have := Nat.div_le_div_right hp.le (c := blockSize N)
  unfold numBlocks
  omega

theorem numBlocks_lt_two_pow_wordLen (N : ℕ) : numBlocks N < 2 ^ wordLen N :=
  Nat.lt_pow_succ_log_self (by decide : 1 < 2) (numBlocks N)

theorem blockSize_le (N : ℕ) : blockSize N ≤ N + 1 := by
  have := Nat.log_le_self 2 N
  unfold blockSize
  omega

theorem numBlocks_le (N : ℕ) : numBlocks N ≤ N + 1 := by
  have := Nat.div_le_self N (blockSize N)
  unfold numBlocks
  omega

theorem log_numBlocks_le (N : ℕ) : Nat.log 2 (numBlocks N) ≤ 5 * blockSize N := by
  have hlog : Nat.log 2 N + 1 ≤ 4 * blockSize N := by
    unfold blockSize
    omega
  have hN : N < 2 ^ (4 * blockSize N) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) hlog)
  have hpow : 2 ^ (4 * blockSize N) < 2 ^ (5 * blockSize N) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by have := blockSize_pos N; omega)
  have hnb : numBlocks N < 2 ^ (5 * blockSize N) := by
    have := numBlocks_le N
    omega
  exact (Nat.log_lt_of_lt_pow (numBlocks_pos N).ne' hnb).le

/-- **Parameter bound**: the output parameter $n = \mathrm{numBlocks}\, N$ satisfies
$n \log_2 n \le 10 N + 5$. -/
theorem numBlocks_mul_log_le (N : ℕ) :
    numBlocks N * Nat.log 2 (numBlocks N) ≤ 10 * N + 5 := by
  have hlog := log_numBlocks_le N
  have hdiv : N / blockSize N * blockSize N ≤ N := Nat.div_mul_le_self N (blockSize N)
  have hbs := blockSize_le N
  calc numBlocks N * Nat.log 2 (numBlocks N)
      ≤ (N / blockSize N + 1) * (5 * blockSize N) := Nat.mul_le_mul_left _ hlog
    _ = 5 * (N / blockSize N * blockSize N) + 5 * blockSize N := by ring
    _ ≤ 5 * N + 5 * (N + 1) := by omega
    _ = 10 * N + 5 := by ring

theorem numAssignments_le (N : ℕ) : numAssignments N ≤ 4 * N + 4 := by
  set k := Nat.log 2 N / 4
  have h2k : 2 * k ≤ Nat.log 2 N := by omega
  have hpow : 2 ^ (2 * k) ≤ N + 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [k]
    · exact (Nat.pow_le_pow_right (by decide : 0 < 2) h2k).trans
        ((Nat.pow_log_le_self 2 (by omega)).trans (Nat.le_succ N))
  have heq : numAssignments N = 4 * 2 ^ (2 * k) := by
    unfold numAssignments blockSize
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    ring
  omega

theorem wordLen_le (N : ℕ) : wordLen N ≤ 6 * blockSize N := by
  have hlog := log_numBlocks_le N
  have hbs := blockSize_pos N
  unfold wordLen
  omega

theorem wordLen_le_two_mul (N : ℕ) : wordLen N ≤ 2 * (N + 1) := by
  have h1 : Nat.log 2 (numBlocks N) ≤ numBlocks N := Nat.log_le_self 2 (numBlocks N)
  have h2 := numBlocks_le N
  unfold wordLen
  omega

theorem searchBits_le_quad (N : ℕ) : searchBits N ≤ 8 * (N + 1) ^ 2 := by
  have hA := numAssignments_le N
  have hW := wordLen_le_two_mul N
  calc searchBits N = numAssignments N * wordLen N := rfl
    _ ≤ (4 * N + 4) * (2 * (N + 1)) := Nat.mul_le_mul hA hW
    _ = 8 * (N + 1) ^ 2 := by ring

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
        _ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right (by decide : 0 < 2) h4k
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
def extractColor (c u : ℕ) : ℕ :=
  (c.testBit (2 * u)).toNat + 2 * (c.testBit (2 * u + 1)).toNat

/-- Check whether a block assignment number $c$ assigns a valid color in $\{0, 1, 2\}$ to every
offset $u < b$. -/
def validAssignment (b c : ℕ) : Bool :=
  (List.range b).all fun u => decide (extractColor c u < 3)

/-- Decode the $v$-th threshold count from the binary digits of $r$, as an $L$-bit word capped at
$n$. -/
def thresholdOf (n L r v : ℕ) : ℕ :=
  Cslib.BitString.boundedBinaryValue n (Cslib.BitString.listRow L v r.bits)

/-- Reconstruct the sorted block assignment $\beta(j) \in \{0, \ldots, B - 1\}$ at sorted position
$j$ from the decoded thresholds: $\beta(j)$ is the number of values $v < B - 1$ whose threshold
$t_v = |\{k < n \mid \beta(k) \le v\}|$ is at most $j$. -/
def bucketOf (B n L r j : ℕ) : ℕ :=
  (List.range (B - 1)).countP fun v => decide (thresholdOf n L r v ≤ j)

/-- The color assigned to local offset $u$ by the $j$-th sorted bucket under threshold table $r$. -/
def colorAt (N r j u : ℕ) : ℕ :=
  extractColor (bucketOf (numAssignments N) (numBlocks N) (wordLen N) r j) u

/-- Edges enforcing $\pi_1(i) = \pi_2(i)$ for all $i < n$. -/
def consistencyEdges (n : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (List.range n).flatMap fun i =>
    (List.range n).flatMap fun j₁ =>
      ((List.range n).filter fun j₂ => !decide (j₁ = j₂)).map fun j₂ => ((i, j₁), (i, j₂))

/-- Self-edges forbidding $\pi_1(i) = j$ when bucket $j$ is not a valid 3-coloring of a block. -/
def invalidBucketEdges (N r : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let b := blockSize N
  let B := numAssignments N
  let n := numBlocks N
  let L := wordLen N
  (List.range n).flatMap fun i =>
    ((List.range n).filter fun j => !validAssignment b (bucketOf B n L r j)).map fun j =>
      ((i, j), (i, j))

/-- Test whether bucket pair $(j_1, j_2)$ creates a color conflict for vertex pair $(p, q)$. -/
def innerConflictTest (N r p q j₁ j₂ : ℕ) : Bool :=
  let b := blockSize N
  let i₁ := p / b
  let u₁ := p % b
  let i₂ := q / b
  let u₂ := q % b
  (!decide (i₁ = i₂) || decide (j₁ = j₂)) &&
    decide (colorAt N r j₁ u₁ = colorAt N r j₂ u₂)

/-- Filtered second-bucket indices $j_2 < n$ that conflict with $(p, q, j_1)$. -/
def innerConflictBuckets (N r p q j₁ : ℕ) : List ℕ :=
  (List.range (numBlocks N)).filter (innerConflictTest N r p q j₁)

/-- Conflict edges for a fixed vertex pair $(p, q)$ and first bucket index $j_1$. -/
def innerConflictEdges (N r p q j₁ : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let b := blockSize N
  let i₁ := p / b
  let i₂ := q / b
  (innerConflictBuckets N r p q j₁).map fun j₂ =>
    ((i₁, j₁), (i₂, j₂))

/-- Conflict edges for a fixed vertex pair $(p, q)$ across all bucket pairs $(j_1, j_2)$. -/
def pairConflictEdges (N r p q : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (List.range (numBlocks N)).flatMap fun j₁ => innerConflictEdges N r p q j₁

/-- Conflict edges incident to vertex position $p$ across all adjacent vertex positions $q$. -/
def vertexConflictEdges (H : Graph) (r p : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let N := H.1.length
  ((List.range N).filter fun q => H.adjBool (H.1.getD p 0) (H.1.getD q 0)).flatMap fun q =>
    pairConflictEdges N r p q

/-- Edges forbidding adjacent vertices $p, q < N$ of $H$ from receiving the same color under the
block assignments selected by $\pi_1(p / b) = j_1$ and $\pi_2(q / b) = j_2$. -/
def conflictEdges (H : Graph) (r : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (List.range H.1.length).flatMap fun p => vertexConflictEdges H r p

/-- The instance of `BipartitePermutationIndependentSet` corresponding to a graph $H$ and a
threshold-table number $r$. -/
def bpisOfColoring (x : Graph × ℕ) : BipartitePermutationGraph :=
  let N := x.1.1.length
  (numBlocks N, consistencyEdges (numBlocks N) ++ invalidBucketEdges N x.2 ++ conflictEdges x.1 x.2)

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
theorem exists_bucketOf_eq_sort (N : ℕ) (a : Fin (numBlocks N) → Fin (numAssignments N)) :
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
theorem exists_block_assignments_of_coloring {N : ℕ} (f : Fin N → Fin 3) :
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
        List.getElem?_eq_getElem (by simp [word]; omega)]
      simp [word, bitFn, Nat.mul_div_right _ (by decide : 0 < 2)]
    have h1 : (a i).val.testBit (2 * u + 1) = decide (col i.val u / 2 = 1) := by
      rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp [word]; omega)]
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

@[fun_prop]
private theorem computableTidilyInPolyTime_listGetDWithInput
    {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} {index : γ → ℕ} (d : α)
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hindex : ComputableTidilyInPolyTime index encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x).getD (index x) d) encIn encA :=
  (listGetD d).comp (hlist.prod hindex)

@[fun_prop]
private theorem computableTidilyInPolyTime_adjBoolWithInput
    {γ : Type} {encIn : γ ↪ List Bool} {G : γ → Graph} {u v : γ → ℕ}
    (hG : ComputableTidilyInPolyTime G encIn encGraph)
    (hu : ComputableTidilyInPolyTime u encIn encNat)
    (hv : ComputableTidilyInPolyTime v encIn encNat) :
    ComputableTidilyInPolyTime (fun x => (G x).adjBool (u x) (v x)) encIn encBool :=
  Graph.computableInPolyTime_adjBool.tidy.comp ((hG.prod hu).prod hv)

@[fun_prop]
private theorem computableTidilyInPolyTime_unary_div'
    {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → ℕ}
    (ha : ComputableTidilyInPolyTime a encIn encUnary)
    (hb : ComputableTidilyInPolyTime b encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => a x / b x) encIn encUnary :=
  unary_div.comp (ha.prod hb)

@[fun_prop]
private theorem computableTidilyInPolyTime_unary_mod'
    {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → ℕ}
    (ha : ComputableTidilyInPolyTime a encIn encUnary)
    (hb : ComputableTidilyInPolyTime b encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => a x % b x) encIn encUnary :=
  unary_mod.comp (ha.prod hb)

@[fun_prop]
private theorem computableTidilyInPolyTime_blockSize :
    ComputableTidilyInPolyTime blockSize encUnary encUnary := by
  unfold blockSize
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_numAssignments :
    ComputableTidilyInPolyTime numAssignments encUnary encUnary := by
  obtain ⟨hefficient, hspec⟩ := iterate_spec (count := fun n => 2 * blockSize n)
    (init := fun _ => 1) (step := fun state => state * 2)
    (encIn := encUnary) (encState := encUnary)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun _ i state => state = 2 ^ i) (fun _ => rfl)
    (fun _ _ _ _ h => by rw [h, pow_succ])
    (size := fun n => 4 * n + 4) (polyBounded (by fun_prop)) (fun n i state hi h => by
      simp only [encUnary_apply, List.length_replicate, h]
      exact (Nat.pow_le_pow_right (by decide : 0 < 2) hi).trans (numAssignments_le n))
  convert hefficient using 1
  funext n
  exact (hspec n).symm

@[fun_prop]
private theorem computableTidilyInPolyTime_numBlocks :
    ComputableTidilyInPolyTime numBlocks encUnary encUnary := by
  unfold numBlocks
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_wordLen :
    ComputableTidilyInPolyTime wordLen encUnary encUnary := by
  unfold wordLen
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_searchBits :
    ComputableTidilyInPolyTime searchBits encUnary encUnary := by
  unfold searchBits
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_extractColor
    {γ : Type} {encIn : γ ↪ List Bool} {c u : γ → ℕ}
    (hc : ComputableTidilyInPolyTime c encIn encUnary)
    (_hu : ComputableTidilyInPolyTime u encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => extractColor (c x) (u x)) encIn encUnary := by
  have hc_bin : ComputableTidilyInPolyTime c encIn encNat := unary_to_binary.comp hc
  unfold extractColor
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_validAssignment
    {γ : Type} {encIn : γ ↪ List Bool} {b c : γ → ℕ}
    (_hb : ComputableTidilyInPolyTime b encIn encUnary)
    (_hc : ComputableTidilyInPolyTime c encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => validAssignment (b x) (c x)) encIn encBool := by
  unfold validAssignment
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_thresholdOf
    {γ : Type} {encIn : γ ↪ List Bool} {n L r v : γ → ℕ}
    (_hn : ComputableTidilyInPolyTime n encIn encUnary)
    (_hL : ComputableTidilyInPolyTime L encIn encUnary)
    (_hr : ComputableTidilyInPolyTime r encIn encNat)
    (_hv : ComputableTidilyInPolyTime v encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => thresholdOf (n x) (L x) (r x) (v x)) encIn encUnary := by
  unfold thresholdOf
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_bucketOf
    {γ : Type} {encIn : γ ↪ List Bool} {B n L r j : γ → ℕ}
    (_hB : ComputableTidilyInPolyTime B encIn encUnary)
    (_hn : ComputableTidilyInPolyTime n encIn encUnary)
    (_hL : ComputableTidilyInPolyTime L encIn encUnary)
    (_hr : ComputableTidilyInPolyTime r encIn encNat)
    (_hj : ComputableTidilyInPolyTime j encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => bucketOf (B x) (n x) (L x) (r x) (j x))
      encIn encUnary := by
  unfold bucketOf
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_colorAt
    {γ : Type} {encIn : γ ↪ List Bool} {N r j u : γ → ℕ}
    (_hN : ComputableTidilyInPolyTime N encIn encUnary)
    (_hr : ComputableTidilyInPolyTime r encIn encNat)
    (_hj : ComputableTidilyInPolyTime j encIn encUnary)
    (_hu : ComputableTidilyInPolyTime u encIn encUnary) :
    ComputableTidilyInPolyTime (fun x => colorAt (N x) (r x) (j x) (u x)) encIn encUnary := by
  unfold colorAt
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_consistencyEdges :
    ComputableTidilyInPolyTime consistencyEdges encUnary
      (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  unfold consistencyEdges
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_invalidBucketEdges :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => invalidBucketEdges p.1 p.2)
      (encPair encUnary encNat)
      (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  unfold invalidBucketEdges
  fun_prop

private theorem computableTidilyInPolyTime_bool_or'
    {α : Type} {encA : α ↪ List Bool} {left right : α → Bool}
    (hleft : ComputableTidilyInPolyTime left encA encBool)
    (hright : ComputableTidilyInPolyTime right encA encBool) :
    ComputableTidilyInPolyTime (fun a => left a || right a) encA encBool :=
  bool_or.comp (hleft.prod hright)

@[fun_prop]
private theorem computableTidilyInPolyTime_innerConflictTest
    {γ : Type} {encIn : γ ↪ List Bool} {N r p q j₁ j₂ : γ → ℕ}
    (_hN : ComputableTidilyInPolyTime N encIn encUnary)
    (_hr : ComputableTidilyInPolyTime r encIn encNat)
    (_hp : ComputableTidilyInPolyTime p encIn encUnary)
    (_hq : ComputableTidilyInPolyTime q encIn encUnary)
    (_hj₁ : ComputableTidilyInPolyTime j₁ encIn encUnary)
    (_hj₂ : ComputableTidilyInPolyTime j₂ encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => innerConflictTest (N x) (r x) (p x) (q x) (j₁ x) (j₂ x))
      encIn encBool := by
  unfold innerConflictTest
  exact bool_and' (computableTidilyInPolyTime_bool_or' (by fun_prop) (by fun_prop)) (by fun_prop)

@[fun_prop]
private theorem computableTidilyInPolyTime_innerConflictBuckets
    {γ : Type} {encIn : γ ↪ List Bool} {N r p q j₁ : γ → ℕ}
    (_hN : ComputableTidilyInPolyTime N encIn encUnary)
    (_hr : ComputableTidilyInPolyTime r encIn encNat)
    (_hp : ComputableTidilyInPolyTime p encIn encUnary)
    (_hq : ComputableTidilyInPolyTime q encIn encUnary)
    (_hj₁ : ComputableTidilyInPolyTime j₁ encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => innerConflictBuckets (N x) (r x) (p x) (q x) (j₁ x))
      encIn (encList encUnary) := by
  unfold innerConflictBuckets
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_innerConflictEdges
    {γ : Type} {encIn : γ ↪ List Bool} {N r p q j₁ : γ → ℕ}
    (_hN : ComputableTidilyInPolyTime N encIn encUnary)
    (_hr : ComputableTidilyInPolyTime r encIn encNat)
    (_hp : ComputableTidilyInPolyTime p encIn encUnary)
    (_hq : ComputableTidilyInPolyTime q encIn encUnary)
    (_hj₁ : ComputableTidilyInPolyTime j₁ encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => innerConflictEdges (N x) (r x) (p x) (q x) (j₁ x))
      encIn (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  unfold innerConflictEdges
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_pairConflictEdges
    {γ : Type} {encIn : γ ↪ List Bool} {N r p q : γ → ℕ}
    (_hN : ComputableTidilyInPolyTime N encIn encUnary)
    (_hr : ComputableTidilyInPolyTime r encIn encNat)
    (_hp : ComputableTidilyInPolyTime p encIn encUnary)
    (_hq : ComputableTidilyInPolyTime q encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => pairConflictEdges (N x) (r x) (p x) (q x))
      encIn (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  unfold pairConflictEdges
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_vertexConflictEdges
    {γ : Type} {encIn : γ ↪ List Bool} {H : γ → Graph} {r p : γ → ℕ}
    (hH : ComputableTidilyInPolyTime H encIn encGraph)
    (_hr : ComputableTidilyInPolyTime r encIn encNat)
    (_hp : ComputableTidilyInPolyTime p encIn encUnary) :
    ComputableTidilyInPolyTime
      (fun x => vertexConflictEdges (H x) (r x) (p x))
      encIn (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  have hverts : ComputableTidilyInPolyTime (fun x => (H x).1) encIn (encList encNat) :=
    (fst (encList encNat) (encList (encPair encNat encNat))).comp hH
  have hlen : ComputableTidilyInPolyTime (fun x => (H x).1.length) encIn encUnary :=
    (length encNat).comp hverts
  unfold vertexConflictEdges
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_conflictEdges :
    ComputableTidilyInPolyTime (fun p : Graph × ℕ => conflictEdges p.1 p.2)
      (encPair encGraph encNat)
      (encList (encPair (encPair encUnary encUnary) (encPair encUnary encUnary))) := by
  have hH : ComputableTidilyInPolyTime (fun p : Graph × ℕ => p.1)
      (encPair encGraph encNat) encGraph := fst encGraph encNat
  have hverts : ComputableTidilyInPolyTime (fun p : Graph × ℕ => p.1.1)
      (encPair encGraph encNat) (encList encNat) :=
    (fst (encList encNat) (encList (encPair encNat encNat))).comp hH
  have hlen : ComputableTidilyInPolyTime (fun p : Graph × ℕ => p.1.1.length)
      (encPair encGraph encNat) encUnary := (length encNat).comp hverts
  unfold conflictEdges
  fun_prop

@[fun_prop]
private theorem computableTidilyInPolyTime_bpisOfColoring :
    ComputableTidilyInPolyTime bpisOfColoring (encPair encGraph encNat)
      encBipartitePermutationGraph := by
  have hH : ComputableTidilyInPolyTime (fun p : Graph × ℕ => p.1)
      (encPair encGraph encNat) encGraph := fst encGraph encNat
  have hverts : ComputableTidilyInPolyTime (fun p : Graph × ℕ => p.1.1)
      (encPair encGraph encNat) (encList encNat) :=
    (fst (encList encNat) (encList (encPair encNat encNat))).comp hH
  have hlen : ComputableTidilyInPolyTime (fun x : Graph × ℕ => x.1.1.length)
      (encPair encGraph encNat) encUnary := (length encNat).comp hverts
  unfold bpisOfColoring encBipartitePermutationGraph
  fun_prop

/-- Constructing `bpisOfColoring (H, r)` is polynomial-time in the plain machine model. -/
@[fun_prop]
theorem computableInPolyTime_bpisOfColoring :
    ComputableInPolyTime bpisOfColoring (encPair encGraph encNat)
      encBipartitePermutationGraph :=
  .of_tidy computableTidilyInPolyTime_bpisOfColoring

@[fun_prop]
private theorem computableTidilyInPolyTime_toBinary :
    ComputableTidilyInPolyTime id encBipartitePermutationGraph
      encBipartitePermutationGraphBinary := by
  have heq : (id : BipartitePermutationGraph → BipartitePermutationGraph) =
      fun G => (G.1, G.2.map fun e => ((e.1.1, e.1.2), (e.2.1, e.2.2))) := by
    funext ⟨n, E⟩
    simp
  rw [heq]
  unfold encBipartitePermutationGraph encBipartitePermutationGraphBinary
  fun_prop

/-- Converting a `BipartitePermutationGraph` from unary to binary coordinate encoding is
polynomial-time in the plain machine model. -/
@[fun_prop]
theorem computableInPolyTime_toBinary :
    ComputableInPolyTime id encBipartitePermutationGraph
      encBipartitePermutationGraphBinary :=
  .of_tidy computableTidilyInPolyTime_toBinary

/-- Constructing `bpisOfColoring (H, r)` under binary coordinate encoding is polynomial-time in the
plain machine model. -/
@[fun_prop]
theorem computableInPolyTime_bpisOfColoring_binary :
    ComputableInPolyTime bpisOfColoring (encPair encGraph encNat)
      encBipartitePermutationGraphBinary :=
  .of_tidy (computableTidilyInPolyTime_toBinary.comp computableTidilyInPolyTime_bpisOfColoring)

/-! ### Exhaustive search over threshold tables and the ETH lower bound -/

private abbrev State : Type := (Graph × ℕ) × Bool

private def encState : State ↪ List Bool :=
  encPair (encPair encGraph encNat) encBool

private def init (H : Graph) : State := ((H, 0), false)

private def step (g : BipartitePermutationGraph → Bool) (s : State) : State :=
  ((s.1.1, s.1.2 + 1), s.2 || g (bpisOfColoring s.1))

private def rounds (H : Graph) : ℕ := 2 ^ searchBits H.1.length

private def search (g : BipartitePermutationGraph → Bool) (H : Graph) : Bool :=
  ((step g)^[rounds H] (init H)).2

private theorem iterate_step_init (g : BipartitePermutationGraph → Bool) (H : Graph) (k : ℕ) :
    (step g)^[k] (init H) =
      ((H, k), (List.range k).any fun r => g (bpisOfColoring (H, r))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, step, List.range_succ, List.any_append,
      List.any_cons, List.any_nil, Bool.or_false]

private theorem search_eq_true_iff {g : BipartitePermutationGraph → Bool}
    (hg : ∀ G, g G = true ↔ G ∈ BipartitePermutationIndependentSet) (H : Graph) :
    search g H = true ↔ H ∈ ThreeColoring := by
  rw [search, iterate_step_init, List.any_eq_true, mem_ThreeColoring_iff_exists_bpisOfColoring]
  simp only [List.mem_range, hg, rounds]

private theorem computableTidilyInPolyTime_init :
    ComputableTidilyInPolyTime init encGraph encState := by
  unfold init encState
  fun_prop

private theorem computableTidilyInPolyTime_rounds :
    ComputableTidilyInPolyTime rounds encGraph encNat := by
  have hlen : ComputableTidilyInPolyTime (fun H : Graph => H.1.length) encGraph encUnary := by
    unfold encGraph
    fun_prop
  unfold rounds
  fun_prop

private theorem exists_computableTidilyInO_step {g : BipartitePermutationGraph → Bool}
    {t : BipartitePermutationGraph → ℕ}
    (hg : ComputableTidilyInO g encBipartitePermutationGraph encBool t t) :
    ∃ d, ComputableTidilyInO (step g) encState encState
      (fun s => ((encState s).length + 1) ^ d + t (bpisOfColoring s.1))
      (fun s => ((encState s).length + 1) ^ d + t (bpisOfColoring s.1)) := by
  obtain ⟨dN, eN, hN⟩ := (show ComputableTidilyInPolyTime (fun s : State => (s.1.1, s.1.2 + 1))
    encState (encPair encGraph encNat) by unfold encState; fun_prop).exists_degree
  obtain ⟨dB, eB, hB⟩ := (show ComputableTidilyInPolyTime (fun s : State => s.2)
    encState encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨dR, eR, hR⟩ := (show ComputableTidilyInPolyTime (fun s : State => bpisOfColoring s.1)
    encState encBipartitePermutationGraph by unfold encState; fun_prop).exists_degree
  obtain ⟨dO, eO, hO⟩ := bool_or.exists_degree
  set D := dN + dB + dR
  have hN' := (hN.mono (d' := D) (e' := eN) (by omega) le_rfl).inO
  have hB' := (hB.mono (d' := D) (e' := eB) (by omega) le_rfl).inO
  have hR' := (hR.mono (d' := D) (e' := eR) (by omega) le_rfl).inO
  have h := hN'.prod (hO.inO.comp (hB'.prod (hg.comp hR')))
  have h4 (p : Bool × Bool) : (encPair encBool encBool p).length = 4 := by simp
  refine ⟨D, (h.mono (5 ^ dO + 4) (fun s => ?_) (fun s => ?_)).of_enc_eq fun _ => rfl⟩ <;>
  · simp only [Function.comp_apply, h4]
    generalize ((encState s).length + 1) ^ D = P
    generalize t (bpisOfColoring s.1) = T
    have hF : 1 ≤ (4 + 1) ^ dO := Nat.one_le_pow _ _ (by norm_num)
    generalize (4 + 1) ^ dO = F at hF ⊢
    nlinarith

private theorem length_encPair_le_of_le_rounds (H : Graph) {k : ℕ} (hk : k ≤ rounds H) :
    (encPair encGraph encNat (H, k)).length ≤ 11 * ((encGraph H).length + 1) ^ 2 := by
  have hK := ComputableTidilyInO.length_encNat_mono hk
  rw [rounds, encNat_two_pow] at hK
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hK
  have hSB := searchBits_le_quad H.1.length
  have hNL := H.length_vertices_le_encGraph
  have hsq : (H.1.length + 1) ^ 2 ≤ ((encGraph H).length + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  simp only [length_encPair]
  nlinarith

private theorem exists_state_and_node_bounds :
    ∃ (c_st c_nd d_nd : ℕ),
      (∀ (g : BipartitePermutationGraph → Bool) (H : Graph) (k : ℕ),
        k ≤ rounds H →
        (encState ((step g)^[k] (init H))).length ≤ c_st * ((encGraph H).length + 1) ^ 2) ∧
      (∀ (H : Graph),
        (encNat (rounds H)).length + 1 ≤ c_st * ((encGraph H).length + 1) ^ 2) ∧
      (∀ (H : Graph) (k : ℕ),
        k ≤ rounds H →
        (encBipartitePermutationGraph (bpisOfColoring (H, k))).length ≤
          c_nd * ((encGraph H).length + 1) ^ d_nd) := by
  obtain ⟨cb, db, hbpis⟩ := computableTidilyInPolyTime_bpisOfColoring.polyBounded_length.exists_le
  refine ⟨24, cb * 12 ^ db, 2 * db, fun g H k hk => ?_, fun H => ?_, fun H k hk => ?_⟩
  · rw [iterate_step_init, encState, length_encPair]
    have hp := length_encPair_le_of_le_rounds H hk
    have h1 : 1 ≤ ((encGraph H).length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    simp only [encBool_apply, List.length_singleton]
    omega
  · rw [rounds, encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hSB := searchBits_le_quad H.1.length
    have hNL := H.length_vertices_le_encGraph
    have hsq : (H.1.length + 1) ^ 2 ≤ ((encGraph H).length + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have h1 : 1 ≤ ((encGraph H).length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    omega
  · have h1 := hbpis (H, k)
    have h2 := length_encPair_le_of_le_rounds H hk
    have h3 : (encPair encGraph encNat (H, k)).length + 1 ≤
        12 * ((encGraph H).length + 1) ^ 2 := by
      have : 1 ≤ ((encGraph H).length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      omega
    calc (encBipartitePermutationGraph (bpisOfColoring (H, k))).length
        ≤ cb * ((encPair encGraph encNat (H, k)).length + 1) ^ db := h1
      _ ≤ cb * (12 * ((encGraph H).length + 1) ^ 2) ^ db :=
          Nat.mul_le_mul_left cb (Nat.pow_le_pow_left h3 db)
      _ = cb * 12 ^ db * ((encGraph H).length + 1) ^ (2 * db) := by
          rw [mul_pow, ← pow_mul, ← mul_assoc]

private noncomputable def leafTime (c_nd d_nd : ℕ) (δ : ℝ) (c e : ℕ) (H : Graph) : ℕ :=
  ⌈(c : ℝ) * (2 ^ (δ * ((10 * H.1.length + 5 : ℕ) : ℝ)) *
    ((c_nd * ((encGraph H).length + 1) ^ d_nd : ℕ) + 1 : ℝ) ^ e) + c⌉₊

/-- **Transfer of exponential-time deciders along the block-sorting reduction**: for every
$M \ge 1$ and $\delta \ge 0$, a decider for `BipartitePermutationIndependentSet` within time
$2^{\delta n \log_2 n} \cdot \mathrm{poly}(|G|)$ yields a decider for `ThreeColoring` within time
$2^{(1 / M + 10 \delta) |V|} \cdot \mathrm{poly}(|H|)$. -/
theorem decidableInExpTime_ThreeColoring_of_bpis {M : ℕ} (hM : 0 < M) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime BipartitePermutationIndependentSet encBipartitePermutationGraph
      (fun G => G.1 * Nat.log 2 G.1) δ) :
    DecidableInExpTime ThreeColoring encGraph (fun H => H.1.length) (1 / M + 10 * δ) := by
  obtain ⟨e, h⟩ := h
  obtain ⟨g, t, c, hg, hgB, ht⟩ := h.exists_computableInO
  have hg := hg.tidy
  obtain ⟨d, hstep⟩ := exists_computableTidilyInO_step hg
  obtain ⟨dn, _, hn⟩ := computableTidilyInPolyTime_rounds.exists_degree
  obtain ⟨di, _, hi⟩ := computableTidilyInPolyTime_init.exists_degree
  obtain ⟨da, _, ha⟩ := (show ComputableTidilyInPolyTime (fun s : State => s.2) encState encBool
    by unfold encState; fun_prop).exists_degree
  obtain ⟨c_st, c_nd, d_nd, hst_bound, hrounds_len, hnd_bound⟩ := exists_state_and_node_bounds
  obtain ⟨K_M, hK_M⟩ : ∃ K_M : ℕ, ∀ N, searchBits N ≤ N / M + K_M :=
    ⟨48 * (48 * M) ^ 3, fun N => searchBits_le_div_add N hM⟩
  set stBound : Graph → ℕ := fun H => c_st * ((encGraph H).length + 1) ^ 2
  set ndBound : Graph → ℕ := fun H => c_nd * ((encGraph H).length + 1) ^ d_nd
  have hround (H : Graph) (k : ℕ) (hk : k ≤ rounds H) :
      ((encState ((step g)^[k] (init H))).length + 1) ^ d +
        t (bpisOfColoring ((step g)^[k] (init H)).1) ≤
        (stBound H + 1) ^ d + leafTime c_nd d_nd δ c e H := by
    have hS : (encState ((step g)^[k] (init H))).length ≤ stBound H := hst_bound g H k hk
    refine Nat.add_le_add (Nat.pow_le_pow_left (by omega) d) ?_
    rw [iterate_step_init]
    dsimp only
    set G := bpisOfColoring (H, k)
    have hG1 : G.1 * Nat.log 2 G.1 ≤ 10 * H.1.length + 5 :=
      numBlocks_mul_log_le H.1.length
    have hGenc : (encBipartitePermutationGraph G).length ≤ ndBound H := hnd_bound H k hk
    have h₁ : (2 : ℝ) ^ (δ * (G.1 * Nat.log 2 G.1 : ℕ)) ≤
        2 ^ (δ * ((10 * H.1.length + 5 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hG1) hδ)
    have h₂ : (((encBipartitePermutationGraph G).length : ℝ) + 1) ^ e ≤
        ((ndBound H : ℝ) + 1) ^ e :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hGenc 1) e
    have h₃ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
    have h₄ := mul_le_mul_of_nonneg_left h₃ (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
    have h₅ := (ht G).trans (add_le_add h₄ le_rfl)
    exact Nat.cast_le.mp (h₅.trans (Nat.le_ceil _))
  have hstate (H : Graph) (k : ℕ) (hk : k ≤ rounds H) :
      (encState ((step g)^[k] (init H))).length ≤ stBound H :=
    hst_bound g H k hk
  have hiter := ComputableTidilyInO.iterate hn.inO hi.inO hstep hround hround hstate
  have hsearch := ha.inO.comp hiter
  set C₁ := (c_st + 1) ^ d + c_st + c_st ^ 2
  set C₃ := (c_st + 1) ^ da
  set E := dn + di + 2 * d + 2 * da + d_nd * e + 4
  set C₂ : ℝ := c * 2 ^ (5 * δ) * ((c_nd : ℝ) + 1) ^ e + c + 1
  set C₀ : ℝ := 3 + C₃ + (2 ^ K_M + 1 : ℝ) * (C₁ + C₂)
  refine DecidableInExpTime.of_computableInO (.of_tidy hsearch)
    (fun H => (search_eq_true_iff (fun G => (hgB G).symm) H).symm) ⌈C₀⌉₊ E fun H => ?_
  set L := (encGraph H).length
  set N := H.1.length
  set P := (L + 1) ^ E
  have hP (a : ℕ) (ha : a ≤ E) : (L + 1) ^ a ≤ P := Nat.pow_le_pow_right (Nat.succ_pos L) ha
  have hsb : stBound H = c_st * (L + 1) ^ 2 := rfl
  have hr : rounds H + 1 ≤ (2 ^ K_M + 1) * 2 ^ (N / M) := by
    have h1 := hK_M N
    have h2 : rounds H ≤ 2 ^ K_M * 2 ^ (N / M) := by
      calc rounds H = 2 ^ searchBits N := rfl
        _ ≤ 2 ^ (N / M + K_M) := Nat.pow_le_pow_right (by decide : 0 < 2) h1
        _ = 2 ^ K_M * 2 ^ (N / M) := by rw [pow_add, Nat.mul_comm]
    have h3 : 1 ≤ 2 ^ (N / M) := Nat.one_le_two_pow
    nlinarith
  have hpoly : (L + 1) ^ dn + (L + 1) ^ di ≤ 2 * P := by
    have := hP dn (by omega)
    have := hP di (by omega)
    omega
  have hans_le : ((encState ((step g)^[rounds H] (init H))).length + 1) ^ da ≤ C₃ * P := by
    have h1 := hstate H (rounds H) le_rfl
    have h2 : stBound H + 1 ≤ (c_st + 1) * (L + 1) ^ 2 := by
      have : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos L)
      rw [hsb]
      nlinarith
    calc ((encState ((step g)^[rounds H] (init H))).length + 1) ^ da
        ≤ (stBound H + 1) ^ da := Nat.pow_le_pow_left (by omega) da
      _ ≤ ((c_st + 1) * (L + 1) ^ 2) ^ da := Nat.pow_le_pow_left h2 da
      _ = C₃ * (L + 1) ^ (2 * da) := by simp only [C₃, mul_pow, ← pow_mul]
      _ ≤ C₃ * P := Nat.mul_le_mul_left C₃ (hP (2 * da) (by omega))
  have hrnd : (stBound H + 1) ^ d + stBound H +
      ((encNat (rounds H)).length + 1) ^ 2 ≤ C₁ * P := by
    have h1 : (stBound H + 1) ^ d ≤ (c_st + 1) ^ d * (L + 1) ^ (2 * d) := by
      have hst1 : stBound H + 1 ≤ (c_st + 1) * (L + 1) ^ 2 := by
        have : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos L)
        rw [hsb]
        nlinarith
      calc (stBound H + 1) ^ d ≤ ((c_st + 1) * (L + 1) ^ 2) ^ d := Nat.pow_le_pow_left hst1 d
        _ = (c_st + 1) ^ d * (L + 1) ^ (2 * d) := by rw [mul_pow, ← pow_mul]
    have h2 : ((encNat (rounds H)).length + 1) ^ 2 ≤ c_st ^ 2 * (L + 1) ^ 4 := by
      have hr_len := hrounds_len H
      calc ((encNat (rounds H)).length + 1) ^ 2
          ≤ (c_st * (L + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hr_len 2
        _ = c_st ^ 2 * (L + 1) ^ 4 := by rw [mul_pow, ← pow_mul]
    have h3 := hP (2 * d) (by omega)
    have h4 := hP 2 (by omega)
    have h5 := hP 4 (by omega)
    calc (stBound H + 1) ^ d + stBound H + ((encNat (rounds H)).length + 1) ^ 2
        ≤ (c_st + 1) ^ d * P + c_st * P + c_st ^ 2 * P := by
          have := h1.trans (Nat.mul_le_mul_left ((c_st + 1) ^ d) h3)
          have := (le_of_eq hsb).trans (Nat.mul_le_mul_left c_st h4)
          have := h2.trans (Nat.mul_le_mul_left (c_st ^ 2) h5)
          omega
      _ = C₁ * P := by simp only [C₁]; ring
  set Y : ℝ := 2 ^ ((10 * δ) * N)
  have hY : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by positivity)
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos L)
  have hleaf : (leafTime c_nd d_nd δ c e H : ℝ) ≤ C₂ * Y * P := by
    have h₁ : (2 : ℝ) ^ (δ * ((10 * N + 5 : ℕ) : ℝ)) = 2 ^ (5 * δ) * Y := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have h₂ : ((ndBound H : ℝ) + 1) ^ e ≤ ((c_nd : ℝ) + 1) ^ e * P := by
      have hnb_le : (ndBound H : ℝ) + 1 ≤ ((c_nd : ℝ) + 1) * ((L : ℝ) + 1) ^ d_nd := by
        have hnb_eq : (ndBound H : ℝ) = c_nd * ((L : ℝ) + 1) ^ d_nd := by
          simp only [ndBound]
          push_cast
          ring
        have hpow1 : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ d_nd :=
          one_le_pow₀ (by linarith [(L.cast_nonneg : (0 : ℝ) ≤ L)])
        nlinarith
      calc ((ndBound H : ℝ) + 1) ^ e ≤ (((c_nd : ℝ) + 1) * ((L : ℝ) + 1) ^ d_nd) ^ e :=
            pow_le_pow_left₀ (by positivity) hnb_le e
        _ = ((c_nd : ℝ) + 1) ^ e * ((L : ℝ) + 1) ^ (d_nd * e) := by rw [mul_pow, ← pow_mul]
        _ ≤ ((c_nd : ℝ) + 1) ^ e * P := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact_mod_cast hP (d_nd * e) (by omega)
    have h₃ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (c : ℝ) * (2 ^ (δ * ((10 * N + 5 : ℕ) : ℝ)) *
      ((ndBound H : ℝ) + 1) ^ e) + c by positivity)
    unfold leafTime
    change (⌈(c : ℝ) * (2 ^ (δ * ((10 * N + 5 : ℕ) : ℝ)) *
      ((ndBound H : ℝ) + 1) ^ e) + c⌉₊ : ℝ) ≤ _
    rw [h₁] at h₃ ⊢
    have h₄ : (c : ℝ) * (2 ^ (5 * δ) * Y * ((ndBound H : ℝ) + 1) ^ e) ≤
        c * 2 ^ (5 * δ) * ((c_nd : ℝ) + 1) ^ e * Y * P := by
      have := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ c * 2 ^ (5 * δ) * Y)
      nlinarith
    have h₅ : (c : ℝ) + 1 ≤ ((c : ℝ) + 1) * Y * P := by
      have : (1 : ℝ) ≤ Y * P := one_le_mul_of_one_le_of_one_le hY hP1
      nlinarith
    calc (⌈(c : ℝ) * (2 ^ (5 * δ) * Y * ((ndBound H : ℝ) + 1) ^ e) + c⌉₊ : ℝ)
        ≤ (c : ℝ) * (2 ^ (5 * δ) * Y * ((ndBound H : ℝ) + 1) ^ e) + c + 1 := h₃.le
      _ ≤ C₂ * Y * P := by simp only [C₂]; nlinarith
  set X : ℝ := 2 ^ ((1 / M : ℝ) * N)
  have hX : ((2 ^ (N / M) : ℕ) : ℝ) ≤ X := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [one_div_mul_eq_div]
    exact Nat.cast_div_le
  have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hXY : X * Y = 2 ^ ((1 / M + 10 * δ) * N) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have hT : ((L + 1) ^ dn + (L + 1) ^ di +
      (rounds H + 1) * ((stBound H + 1) ^ d + leafTime c_nd d_nd δ c e H +
        stBound H + ((encNat (rounds H)).length + 1) ^ 2) +
      ((encState ((step g)^[rounds H] (init H))).length + 1) ^ da : ℝ) ≤
      (2 + C₃ : ℝ) * P + (2 ^ K_M + 1 : ℝ) * X * (C₁ * P + C₂ * Y * P) := by
    have h₁ : ((L + 1) ^ dn + (L + 1) ^ di : ℝ) ≤ 2 * P := by exact_mod_cast hpoly
    have h₁' : (((encState ((step g)^[rounds H] (init H))).length + 1) ^ da : ℝ) ≤ C₃ * P := by
      exact_mod_cast hans_le
    have h₂ : ((rounds H + 1 : ℕ) : ℝ) ≤ (2 ^ K_M + 1 : ℝ) * X := by
      have : ((rounds H + 1 : ℕ) : ℝ) ≤ (((2 ^ K_M + 1) * 2 ^ (N / M) : ℕ) : ℝ) := by
        exact_mod_cast hr
      rw [Nat.cast_mul] at this
      have hKM : (0 : ℝ) ≤ (2 ^ K_M + 1 : ℕ) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hX hKM
      push_cast at this hmul ⊢
      linarith
    have h₃ : (((stBound H + 1) ^ d + stBound H +
        ((encNat (rounds H)).length + 1) ^ 2 : ℕ) : ℝ) ≤ C₁ * P := by exact_mod_cast hrnd
    have h₄ : (((stBound H + 1) ^ d + leafTime c_nd d_nd δ c e H + stBound H +
        ((encNat (rounds H)).length + 1) ^ 2 : ℕ) : ℝ) ≤ C₁ * P + C₂ * Y * P := by
      push_cast at h₃ ⊢
      linarith
    have h₅ := mul_le_mul h₂ h₄ (by positivity) (by positivity)
    push_cast at h₁ h₁' h₅ ⊢
    linarith
  calc _ ≤ (2 + C₃ : ℝ) * P + (2 ^ K_M + 1 : ℝ) * X * (C₁ * P + C₂ * Y * P) := by
          exact_mod_cast hT
    _ ≤ C₀ * (X * Y * P) := by
        have hXY1 : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hX1 hY
        have hC₂ : 0 ≤ C₂ := by positivity
        have hC₁ : (0 : ℝ) ≤ C₁ := by positivity
        have hC₃ : (0 : ℝ) ≤ C₃ := by positivity
        have hKM : (0 : ℝ) ≤ 2 ^ K_M + 1 := by positivity
        have hP0 : (0 : ℝ) ≤ P := by positivity
        have a₁ : (P : ℝ) ≤ X * Y * P := le_mul_of_one_le_left hP0 hXY1
        have a₂ : X * P ≤ X * Y * P := by
          have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ X * P)
          linarith [show X * P * Y = X * Y * P by ring]
        have a₃ := mul_le_mul_of_nonneg_left a₂ (mul_nonneg hKM hC₁)
        have a₄ := mul_le_mul_of_nonneg_left a₁ hC₃
        simp only [C₀]
        nlinarith
    _ ≤ ⌈C₀⌉₊ * (2 ^ ((1 / M + 10 * δ) * N) * ((L : ℝ) + 1) ^ E) := by
        rw [← hXY]
        push_cast [P]
        exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₀) (by positivity)

end BipartitePermutationIndependentSet

open BipartitePermutationIndependentSet in
/-- **Subexponential-time transfer from `BipartitePermutationIndependentSet` to `ThreeColoring`**:
if `BipartitePermutationIndependentSet` is decidable in time $2^{o(n \log n)}$, then
`ThreeColoring` is decidable in time $2^{o(|V|)}$. -/
theorem DecidableInSubexpTime.threeColoring_of_bipartitePermutationIndependentSet
    (h : DecidableInSubexpTime BipartitePermutationIndependentSet encBipartitePermutationGraph
      fun G => G.1 * Nat.log 2 G.1) :
    DecidableInSubexpTime ThreeColoring encGraph fun H => H.1.length := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM_nat : 0 < M := Nat.cast_pos.mp hMpos
  have hMε : 1 / (M : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hM
    linarith
  set δ := ε / 20
  have hδ : 0 < δ := by positivity
  refine (decidableInExpTime_ThreeColoring_of_bpis hM_nat hδ.le (h δ hδ)).mono ?_
  simp only [δ]
  linarith

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
        rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
        exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) G.1).le
      have h2 : 1 ≤ Nat.log 2 G.1 := Nat.log_pos (by decide : 1 < 2) hG
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
        rw [Nat.mul_comm, Nat.log_mul_base (by decide : 1 < 2) (by omega)]
      have h2 : 1 ≤ Nat.log 2 G.1 := Nat.log_pos (by decide : 1 < 2) hG
      omega
    calc (2 * G.1) * Nat.log 2 (2 * G.1)
        ≤ (2 * G.1) * (2 * Nat.log 2 G.1) := Nat.mul_le_mul_left _ hlog
      _ ≤ 4 * (G.1 * Nat.log 2 G.1) + 4 := by ring_nf; omega

end Cslib.Complexity
