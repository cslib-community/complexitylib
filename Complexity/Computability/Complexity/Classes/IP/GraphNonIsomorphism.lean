/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.Guessing
public import Complexity.Computability.Complexity.Classes.IP.Repetition
public import Complexity.Computability.Complexity.Problems.GraphIsomorphism
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Foundations.Data.List.OfFn
import Complexity.Probability.BitString.List

/-!
# Graph non-isomorphism has an interactive proof

The private-coin protocol of Goldreich, Micali and Wigderson
[GoldreichMicaliWigderson1991], [Arora and Barak, Section 8.1.3][AroraBarak09]: the verifier picks
one of the two graphs at random, sends the prover a random relabeling of it, and accepts when the
prover names the graph it picked. On non-isomorphic graphs the relabelings of the two graphs are
different graphs, so an unbounded prover always names the right one. On isomorphic graphs they
have the same distribution, so no prover is right with probability more than `1 / 2`.

With a uniformly random relabeling the two message laws would be equal on isomorphic graphs and
one round would have soundness error exactly `1 / 2` (`acceptProb_guessingRound_le_half`). A strict
fair-coin verifier cannot sample a uniformly random permutation of `n` vertices exactly when `n!` is
not a power of two. The verifier here relabels by random keys instead: it draws an
independent key of `keyWidth n` bits for each of the `n` distinct vertices, with
`2 ^ keyWidth n ≥ 16 * n * n`, and sends the adjacency matrix with the vertices listed in
increasing order of their keys, ties broken by position (`relabel`). Completeness stays exactly
`1`, since every relabeling is isomorphic to the graph it came from
(`exists_equiv_of_relabelFin_eq`). When the keys are distinct, relabeling isomorphic graphs gives
exactly the same distribution (`relabelFin_comp`), and keys collide with probability at most
`1 / 16` by the birthday bound. One round therefore has soundness error `17 / 32`
(`acceptProb_round_le`), and two sequential rounds `(17 / 32) ^ 2 < 1 / 3`.

## Main definitions

* `Cslib.Complexity.GraphNonIsomorphism.relabel`: the adjacency matrix of a graph listed in key
  order.
* `Cslib.Complexity.GraphNonIsomorphism.relabelMessage`: a relabeling by random keys.
* `Cslib.Complexity.GraphNonIsomorphism.round`, `.verifier`, `.prover`: the protocol.

## Main results

* `Cslib.Complexity.GraphNonIsomorphism.tsum_relabelDist_le`: relabelings of isomorphic graphs are
  `1 / 16`-close.
* `Cslib.Complexity.GraphNonIsomorphism.isInteractiveProof_round`: completeness `1` and soundness
  error `17 / 32` per round.
* `Cslib.Complexity.GraphNonIsomorphism.isInteractiveProof_verifier`,
  `Cslib.Complexity.GraphNonIsomorphism.isOraclePPTOn_verifier`,
  `Cslib.Complexity.GraphNonIsomorphism.mem_IP`: `GraphNonIsomorphism ∈ IP`.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that yield nothing but their validity or all
  languages in NP have zero-knowledge proof systems*][GoldreichMicaliWigderson1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM ComputableTidilyInPolyTime

namespace GraphNonIsomorphism

/-! ### Ranking positions by keys -/

variable {n : ℕ}

/-- The rank of position `i` when positions are ordered by their keys `k`, ties broken by
position. -/
def keyRank (k : Fin n → ℕ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => k j < k i ∨ (k j = k i ∧ j < i)).card

theorem keyRank_lt (k : Fin n → ℕ) (i : Fin n) : keyRank k i < n := by
  unfold keyRank
  calc (Finset.univ.filter fun j => k j < k i ∨ (k j = k i ∧ j < i)).card
      < (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.2 ⟨i, by simp, ?_⟩
        simp
    _ = n := by simp

private theorem keyRank_lt_keyRank (k : Fin n → ℕ) {i j : Fin n}
    (h : k i < k j ∨ (k i = k j ∧ i < j)) :
    keyRank k i < keyRank k j := by
  unfold keyRank
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i, by simpa using h, by simp⟩
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  omega

theorem keyRank_injective (k : Fin n → ℕ) : Function.Injective (keyRank k) := by
  intro i j h
  by_contra hij
  rcases lt_trichotomy (k i) (k j) with hk | hk | hk
  · exact (keyRank_lt_keyRank k (Or.inl hk)).ne h
  · rcases lt_or_gt_of_ne hij with hl | hl
    · exact (keyRank_lt_keyRank k (Or.inr ⟨hk, hl⟩)).ne h
    · exact (keyRank_lt_keyRank k (Or.inr ⟨hk.symm, hl⟩)).ne' h
  · exact (keyRank_lt_keyRank k (Or.inl hk)).ne' h

/-- Ordering positions by key, ties broken by position, as a permutation. -/
noncomputable def rankPerm (k : Fin n → ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => ⟨keyRank k i, keyRank_lt k i⟩)
    (Finite.injective_iff_bijective.1 fun _ _ h => keyRank_injective k (congrArg Fin.val h))

@[simp] theorem rankPerm_apply (k : Fin n → ℕ) (i : Fin n) : (rankPerm k i : ℕ) = keyRank k i :=
  rfl

/-- With distinct keys, permuting the positions permutes the ranks. -/
private theorem keyRank_comp {k : Fin n → ℕ} (hk : Function.Injective k) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : keyRank (k ∘ σ) i = keyRank k (σ i) := by
  have hsimp (k : Fin n → ℕ) (hk : Function.Injective k) (i : Fin n) :
      keyRank k i = (Finset.univ.filter fun j => k j < k i).card := by
    unfold keyRank
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact h
      · exact absurd (hk h ▸ h') (lt_irrefl _)
    · exact Or.inl
  rw [hsimp _ (hk.comp σ.injective), hsimp _ hk]
  refine Finset.card_bij (fun j _ => σ j) (by simp) (fun _ _ _ _ h => σ.injective h) ?_
  intro j hj
  exact ⟨σ.symm j, by simpa using hj, by simp⟩

private theorem rankPerm_comp {k : Fin n → ℕ} (hk : Function.Injective k) (σ : Equiv.Perm (Fin n)) :
    rankPerm (k ∘ σ) = σ.trans (rankPerm k) := by
  ext i
  simp [keyRank_comp hk]

/-! ### Relabeled adjacency matrices -/

/-- The adjacency matrix `A`, listed row by row with positions in increasing order of keys. -/
noncomputable def relabelFin (A : Fin n → Fin n → Bool) (k : Fin n → ℕ) : List Bool :=
  List.ofFn fun t : Fin (n * n) =>
    A ((rankPerm k).symm (finProdFinEquiv.symm t).1) ((rankPerm k).symm (finProdFinEquiv.symm t).2)

private theorem relabelFin_eq_flatten (A : Fin n → Fin n → Bool) (k : Fin n → ℕ) :
    relabelFin A k = (List.ofFn fun r : Fin n => List.ofFn fun s : Fin n =>
      A ((rankPerm k).symm r) ((rankPerm k).symm s)).flatten := by
  rw [relabelFin, List.ofFn_mul]
  congr 2
  funext r
  congr 1
  funext s
  have : (⟨r * n + s, by nlinarith [r.isLt, s.isLt]⟩ : Fin (n * n)) = finProdFinEquiv (r, s) := by
    ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [this, Equiv.symm_apply_apply]

/-- With distinct keys, isomorphic adjacency matrices are relabeled alike by permuted keys. -/
theorem relabelFin_comp {A A' : Fin n → Fin n → Bool} {k : Fin n → ℕ}
    (hk : Function.Injective k) (σ : Equiv.Perm (Fin n)) (hA : ∀ i j, A' (σ i) (σ j) = A i j) :
    relabelFin A' k = relabelFin A (k ∘ σ) := by
  rw [relabelFin, relabelFin, rankPerm_comp hk]
  congr
  funext t
  simp only [Equiv.symm_trans_apply]
  rw [← hA, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Equal relabelings come from isomorphic adjacency matrices. -/
theorem exists_equiv_of_relabelFin_eq {n' : ℕ} {A : Fin n → Fin n → Bool}
    {A' : Fin n' → Fin n' → Bool} {k : Fin n → ℕ} {k' : Fin n' → ℕ}
    (h : relabelFin A k = relabelFin A' k') :
    ∃ σ : Fin n ≃ Fin n', ∀ i j, A' (σ i) (σ j) = A i j := by
  obtain ⟨hnn, hf⟩ := Sigma.mk.inj_iff.1 (List.ofFn_inj'.1 h)
  obtain rfl : n = n' := Nat.mul_self_inj.1 hnn
  have hf := eq_of_heq hf
  refine ⟨(rankPerm k).trans (rankPerm k').symm, fun i j => ?_⟩
  have := congrFun hf (finProdFinEquiv (rankPerm k i, rankPerm k j))
  simp only [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  simpa using this.symm

/-! ### Computing relabelings -/

/-- The key of position `i` below `n`; missing entries read as `0`. -/
private def keyAt (n : ℕ) (keys : List ℕ) (i : Fin n) : ℕ := keys.getD i 0

/-- The rank of position `i` among the positions below `n`, ordered by the entries of `keys`
(missing entries read as `0`), ties broken by position. -/
def rankOf (n : ℕ) (keys : List ℕ) (i : ℕ) : ℕ :=
  (List.range n).countP fun j =>
    decide (keys.getD j 0 < keys.getD i 0) ||
      decide (keys.getD j 0 = keys.getD i 0) && decide (j < i)

/-- The positions below `n` in increasing order of rank. -/
def orderOf (n : ℕ) (keys : List ℕ) : List ℕ :=
  (List.range n).map fun r => ((List.range n).filter fun i => decide (rankOf n keys i = r)).headD 0

/-- The adjacency matrix of `G` with its distinct vertices listed in increasing order of `keys`. -/
def relabel (G : Graph) (keys : List ℕ) : List Bool :=
  (orderOf G.distinctVertices.length keys).flatMap fun u =>
    (orderOf G.distinctVertices.length keys).map fun v => G.adjIndex u v

private theorem rankOf_eq (n : ℕ) (keys : List ℕ) (i : Fin n) :
    rankOf n keys i = keyRank (keyAt n keys) i := by
  rw [rankOf, List.countP_range_eq_card_filter, keyRank]
  congr 1

private theorem filter_rankOf_eq (n : ℕ) (keys : List ℕ) (r : Fin n) :
    (List.range n).filter (fun i => decide (rankOf n keys i = r)) =
      [((rankPerm (keyAt n keys)).symm r : ℕ)] := by
  rw [List.filter_congr (q := fun i => decide (i = ((rankPerm (keyAt n keys)).symm r : ℕ))),
    List.filter_eq, List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 (Fin.isLt _)),
    List.replicate_one]
  intro i hi
  have hi := List.mem_range.1 hi
  rw [rankOf_eq n keys ⟨i, hi⟩, ← rankPerm_apply, decide_eq_decide]
  rw [← Fin.ext_iff, ← Equiv.eq_symm_apply, Fin.ext_iff]

private theorem orderOf_eq (n : ℕ) (keys : List ℕ) :
    orderOf n keys = List.ofFn fun r : Fin n => ((rankPerm (keyAt n keys)).symm r : ℕ) := by
  apply List.ext_getElem (by simp [orderOf])
  intro r h1 h2
  simp only [orderOf, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have := filter_rankOf_eq n keys ⟨r, by simpa using h2⟩
  simp only at this
  rw [this]
  rfl

/-- The adjacency matrix of `G` on the positions of its distinct vertices. -/
private def adjFin (G : Graph) (i j : Fin G.distinctVertices.length) : Bool := G.adjIndex i j

private theorem relabel_eq (G : Graph) (keys : List ℕ) :
    relabel G keys = relabelFin (adjFin G) (keyAt G.distinctVertices.length keys) := by
  rw [relabel, orderOf_eq, relabelFin_eq_flatten, List.flatMap_def, List.map_ofFn]
  congr 1
  simp [Function.comp_def, List.map_ofFn, adjFin]

@[fun_prop]
private theorem natGetD {γ : Type} {input : γ ↪ List Bool} {list : γ → List ℕ} {index : γ → ℕ}
    (hlist : ComputableTidilyInPolyTime list input (encList encUnary))
    (hindex : ComputableTidilyInPolyTime index input encUnary) :
    ComputableTidilyInPolyTime (fun x => (list x).getD (index x) 0) input encUnary :=
  (listGetD (encA := encUnary) 0).comp (hlist.prod hindex)

@[fun_prop]
theorem computableInPolyTime_rankOf {γ : Type} {input : γ ↪ List Bool} {n i : γ → ℕ}
    {keys : γ → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hkeys : ComputableInPolyTime keys input (encList encUnary))
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun x => rankOf (n x) (keys x) (i x)) input encUnary := by
  have hn := hn.tidy
  have hkeys := hkeys.tidy
  have hi := hi.tidy
  refine .of_tidy ?_
  unfold rankOf
  fun_prop

@[fun_prop]
theorem computableInPolyTime_orderOf {γ : Type} {input : γ ↪ List Bool} {n : γ → ℕ}
    {keys : γ → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hkeys : ComputableInPolyTime keys input (encList encUnary)) :
    ComputableInPolyTime (fun x => orderOf (n x) (keys x)) input (encList encUnary) := by
  unfold orderOf
  fun_prop

@[fun_prop]
theorem computableInPolyTime_relabel {γ : Type} {input : γ ↪ List Bool} {G : γ → Graph}
    {keys : γ → List ℕ} (hG : ComputableInPolyTime G input encGraph)
    (hkeys : ComputableInPolyTime keys input (encList encUnary)) :
    ComputableInPolyTime (fun x => relabel (G x) (keys x)) input encBits := by
  have hn : ComputableInPolyTime (fun x => (G x).distinctVertices.length) input encUnary :=
    (ComputableInPolyTime.length_list encNat).comp
      (Graph.computableInPolyTime_distinctVertices.comp hG)
  unfold relabel
  simp only [List.flatMap_def]
  fun_prop

/-! ### Relabeling by random keys -/

/-- The value of a key of `w` bits, read most significant bit first. -/
def keyValue {w : ℕ} (row : BitString w) : ℕ :=
  BitString.boundedBinaryValue (2 ^ w) (List.ofFn row)

theorem keyValue_injective (w : ℕ) : Function.Injective (keyValue (w := w)) := by
  intro r r' h
  have hlt (r : BitString w) : BitString.binaryValue (List.ofFn r) ≤ 2 ^ w := by
    simpa using (BitString.binaryValue_lt_two_pow (List.ofFn r)).le
  simp only [keyValue, BitString.boundedBinaryValue_eq, Nat.min_eq_right (hlt _)] at h
  exact List.ofFn_injective (BitString.binaryValue_injective_of_length_eq (by simp) h)

/-- Keys of `keyWidth n` bits take at least `16 * n * n` values. -/
def keyWidth (n : ℕ) : ℕ := Nat.clog 2 (16 * n * n)

/-- The keys read from the first `n` consecutive `w`-bit rows of a word. -/
def keysOf (n w : ℕ) (bits : List Bool) : List ℕ :=
  (BitString.listRows n w bits).map (BitString.boundedBinaryValue (2 ^ w))

/-- The verifier's message about `G`: its adjacency matrix with the distinct vertices listed in
the order of independent uniform keys of `keyWidth` bits, ties broken by position. -/
noncomputable def relabelMessage (G : Graph) : ProbComp (List Bool) :=
  (fun bits => relabel G (keysOf G.distinctVertices.length (keyWidth G.distinctVertices.length)
    bits)) <$> BitString.sampleList (G.distinctVertices.length * keyWidth G.distinctVertices.length)

/-- The distribution of relabelings of the adjacency matrix `A` on `n` positions. -/
noncomputable def relabelDist (n : ℕ) (A : Fin n → Fin n → Bool) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Fin n → BitString (keyWidth n))).map fun R => relabelFin A (keyValue ∘ R)

private theorem eval_relabelMessage (G : Graph) :
    ProbComp.eval (relabelMessage G) = relabelDist G.distinctVertices.length (adjFin G) := by
  set n := G.distinctVertices.length
  rw [relabelMessage, ProbComp.eval_map, BitString.eval_sampleList,
    show (fun bits => relabel G (keysOf n (keyWidth n) bits)) =
      (fun rows => relabel G (rows.map (BitString.boundedBinaryValue (2 ^ keyWidth n)))) ∘
        BitString.listRows n (keyWidth n) from rfl,
    ← PMF.map_comp, BitString.uniformList_listRows, PMF.map_comp, relabelDist]
  congr 1
  funext R
  simp only [Function.comp_apply, relabel_eq]
  congr 1
  funext i
  simp [keyAt, keyValue, List.getD_eq_getElem?_getD, n]

/-! ### Hiding -/

/-- A birthday bound on falling factorials. -/
private theorem pow_succ_le_descFactorial_add (D n : ℕ) :
    D ^ (n + 1) ≤ D.descFactorial (n + 1) + (n + 1) ^ 2 * D ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdesc : D * D.descFactorial (n + 1) ≤
        D.descFactorial (n + 2) + (n + 1) * D.descFactorial (n + 1) := by
      rw [Nat.descFactorial_succ D (n + 1), ← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    have hle := Nat.descFactorial_le_pow D (n + 1)
    calc D ^ (n + 2) = D * D ^ (n + 1) := by ring
      _ ≤ D * (D.descFactorial (n + 1) + (n + 1) ^ 2 * D ^ n) := Nat.mul_le_mul_left _ ih
      _ = D * D.descFactorial (n + 1) + (n + 1) ^ 2 * D ^ (n + 1) := by ring
      _ ≤ D.descFactorial (n + 2) + (n + 1) * D ^ (n + 1) + (n + 1) ^ 2 * D ^ (n + 1) := by
        have := Nat.mul_le_mul_left (n + 1) hle
        omega
      _ ≤ D.descFactorial (n + 2) + (n + 2) ^ 2 * D ^ (n + 1) := by
        have : (n + 1) * D ^ (n + 1) + (n + 1) ^ 2 * D ^ (n + 1) ≤ (n + 2) ^ 2 * D ^ (n + 1) := by
          rw [← Nat.add_mul]
          exact Nat.mul_le_mul_right _ (by nlinarith)
        omega

open Classical in
/-- **Birthday bound.** Among the functions from `Fin n` to a finite type with `D` elements, the
non-injective ones are at most a fraction `n ^ 2 / D`. -/
private theorem card_filter_not_injective_mul_le (n : ℕ) (β : Type*) [Fintype β] [DecidableEq β] :
    (Finset.univ.filter fun R : Fin n → β => ¬ Function.Injective R).card * Fintype.card β ≤
      n ^ 2 * Fintype.card β ^ n := by
  have hinj : (Finset.univ.filter fun R : Fin n → β => Function.Injective R).card =
      (Fintype.card β).descFactorial n := by
    rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
      Fintype.card_embedding_eq, Fintype.card_fin]
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun R : Fin n → β => Function.Injective R)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hinj] at hsum
  cases n with
  | zero =>
    have : (Finset.univ.filter fun R : Fin 0 → β => ¬ Function.Injective R) = ∅ := by
      ext R
      simp [Function.injective_of_subsingleton R]
    rw [this, Finset.card_empty, zero_mul]
    exact Nat.zero_le _
  | succ m =>
    have := pow_succ_le_descFactorial_add (Fintype.card β) m
    calc (Finset.univ.filter fun R : Fin (m + 1) → β => ¬ Function.Injective R).card *
          Fintype.card β ≤ ((m + 1) ^ 2 * Fintype.card β ^ m) * Fintype.card β :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (m + 1) ^ 2 * Fintype.card β ^ (m + 1) := by ring

open Classical in
/-- Random keys collide with probability at most `1 / 16`. -/
private theorem card_filter_not_injective_div_le (n : ℕ) :
    ((Finset.univ.filter fun R : Fin n → BitString (keyWidth n) =>
      ¬ Function.Injective R).card : ENNReal) /
      Fintype.card (Fin n → BitString (keyWidth n)) ≤ 1 / 16 := by
  have hbound := card_filter_not_injective_mul_le n (BitString (keyWidth n))
  have hclog : 16 * n * n ≤ Fintype.card (BitString (keyWidth n)) := by
    rw [show Fintype.card (BitString (keyWidth n)) = 2 ^ keyWidth n by simp [BitString]]
    exact Nat.le_pow_clog (by norm_num) _
  have hcard : Fintype.card (Fin n → BitString (keyWidth n)) =
      Fintype.card (BitString (keyWidth n)) ^ n := by simp
  have hzero : n = 0 → (Finset.univ.filter fun R : Fin n → BitString (keyWidth n) =>
      ¬ Function.Injective R).card = 0 := by
    rintro rfl
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun R _ h => h (Function.injective_of_subsingleton R)
  have hDpos : 0 < Fintype.card (BitString (keyWidth n)) := Fintype.card_pos
  rw [hcard]
  generalize Fintype.card (BitString (keyWidth n)) = D at *
  generalize (Finset.univ.filter fun R : Fin n → BitString (keyWidth n) =>
      ¬ Function.Injective R).card = bad at *
  have key : bad * 16 ≤ D ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hzero rfl]
    · have : bad * 16 * (n * n) ≤ D ^ n * (n * n) :=
        calc bad * 16 * (n * n) = bad * (16 * n * n) := by ring
          _ ≤ bad * D := Nat.mul_le_mul_left _ hclog
          _ ≤ n ^ 2 * D ^ n := hbound
          _ = D ^ n * (n * n) := by ring
      exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos hn hn)
  rw [ENNReal.div_le_iff (by exact_mod_cast (pow_pos hDpos n).ne') (by simp), one_div,
    ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  exact_mod_cast key

/-- Expectations after a deterministic map are expectations of the composite. -/
private theorem tsum_map_mul {β γ : Type*} (μ : PMF β) (m : β → γ) (f : γ → ENNReal) :
    ∑' c, μ.map m c * f c = ∑' b, μ b * f (m b) := by
  simp only [PMF.map_apply, ENNReal.tsum_mul_right.symm]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => ?_
  rw [tsum_eq_single (m b)]
  · simp
  · intro c hc
    simp [hc]

/-- Two deterministic views of a uniform sample that agree up to a relabeling of the sample
outside a set of bad samples are close: their expectations of `[0, 1]`-valued functions differ by
at most the probability of a bad sample. -/
private theorem tsum_uniform_map_le {β γ : Type*} [Fintype β] [Nonempty β] (m₀ m₁ : β → γ)
    (e : β ≃ β) (good : β → Prop) [DecidablePred good] (heq : ∀ b, good b → m₁ b = m₀ (e b))
    {f : γ → ENNReal} (hf : ∀ c, f c ≤ 1) :
    ∑' c, (PMF.uniformOfFintype β).map m₁ c * f c ≤
      ∑' c, (PMF.uniformOfFintype β).map m₀ c * f c +
        (Finset.univ.filter fun b => ¬ good b).card / Fintype.card β := by
  simp only [tsum_map_mul, tsum_fintype, PMF.uniformOfFintype_apply, ← Finset.mul_sum]
  rw [ENNReal.div_eq_inv_mul, ← mul_add]
  gcongr
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ good]
  gcongr
  · calc ∑ b ∈ Finset.univ.filter good, f (m₁ b)
        = ∑ b ∈ Finset.univ.filter good, f (m₀ (e b)) :=
          Finset.sum_congr rfl fun b hb => by rw [heq b (Finset.mem_filter.1 hb).2]
      _ ≤ ∑ b, f (m₀ (e b)) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ∑ b, f (m₀ b) := e.sum_comp (fun b => f (m₀ b))
  · calc ∑ b ∈ Finset.univ.filter (fun b => ¬ good b), f (m₁ b)
        ≤ ∑ b ∈ Finset.univ.filter (fun b => ¬ good b), (1 : ENNReal) :=
          Finset.sum_le_sum fun b _ => hf _
      _ = _ := by simp

open Classical in
/-- **Hiding.** Relabelings of isomorphic adjacency matrices are `1 / 16`-close: on distinct keys
they have exactly the same law, and keys collide with probability at most `1 / 16`. -/
theorem tsum_relabelDist_le {n n' : ℕ} {A : Fin n → Fin n → Bool} {A' : Fin n' → Fin n' → Bool}
    (σ : Fin n ≃ Fin n') (hσ : ∀ i j, A' (σ i) (σ j) = A i j) {f : List Bool → ENNReal}
    (hf : ∀ m, f m ≤ 1) :
    ∑' m, relabelDist n' A' m * f m ≤ ∑' m, relabelDist n A m * f m + 1 / 16 := by
  obtain rfl : n = n' := Fin.equiv_iff_eq.1 ⟨σ⟩
  refine (tsum_uniform_map_le (fun R => relabelFin A (keyValue ∘ R))
    (fun R => relabelFin A' (keyValue ∘ R)) (Equiv.arrowCongr σ.symm (Equiv.refl _))
    (fun R => Function.Injective R) (fun R hR => ?_) hf).trans ?_
  · rw [relabelFin_comp ((keyValue_injective _).comp hR) σ hσ]
    rfl
  · exact add_le_add le_rfl (card_filter_not_injective_div_le n)

/-- Equal relabelings come from isomorphic adjacency matrices. -/
private theorem exists_equiv_of_mem_support_relabelDist {n n' : ℕ} {A : Fin n → Fin n → Bool}
    {A' : Fin n' → Fin n' → Bool} {m : List Bool} (hm : m ∈ (relabelDist n A).support)
    (hm' : m ∈ (relabelDist n' A').support) :
    ∃ σ : Fin n ≃ Fin n', ∀ i j, A' (σ i) (σ j) = A i j := by
  obtain ⟨R, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
  obtain ⟨R', -, h⟩ := (PMF.mem_support_map_iff _ _ _).1 hm'
  exact exists_equiv_of_relabelFin_eq h.symm

/-! ### The protocol -/

/-- The message of the protocol for the secret bit `b`: a random relabeling of the second graph
when `b` is `true`, of the first otherwise. -/
noncomputable def message (x : Graph × Graph) (b : Bool) : ProbComp (List Bool) :=
  relabelMessage (if b then x.2 else x.1)

/-- One round of the private-coin protocol of Goldreich, Micali and Wigderson: the verifier picks
one of the two graphs at random, sends a random relabeling of it, and accepts when the prover
names the graph it picked. -/
noncomputable def round (x : Graph × Graph) : WordOracleComp Unit Bool := guessingRound (message x)

/-- The verifier: two sequential rounds. -/
noncomputable def verifier (x : Graph × Graph) : WordOracleComp Unit Bool :=
  sequentialRepeat 2 (round x)

/-- The honest prover: name the graph of which the message is a possible relabeling. -/
noncomputable def prover (x : Graph × Graph) : Prover Unit := guessingProver (message x)

private theorem eval_message (x : Graph × Graph) (b : Bool) : ProbComp.eval (message x b) =
    relabelDist (if b then x.2 else x.1).distinctVertices.length
      (adjFin (if b then x.2 else x.1)) := eval_relabelMessage _

/-- **Soundness of one round.** On isomorphic graphs every prover names the picked graph with
probability at most `17 / 32`: one half, plus half the key collision probability. -/
theorem acceptProb_round_le {x : Graph × Graph} (hx : x ∈ GraphIsomorphism) (P : Prover Unit) :
    acceptProb (round x) P ≤ 17 / 32 := by
  obtain ⟨σ, hσ⟩ := mem_GraphIsomorphism_iff.1 hx
  refine (acceptProb_guessingRound_le (δ := 1 / 16) (fun f hf => ?_) P).trans_eq ?_
  · simp only [eval_message]
    exact tsum_relabelDist_le σ hσ hf
  · have h1 : ((17 : ENNReal) / 32) = ((17 / 32 : NNReal) : ENNReal) := by
      rw [ENNReal.coe_div (by norm_num)]; norm_num
    have h2 : ((1 : ENNReal) + 1 / 16) / 2 = (((1 + 1 / 16) / 2 : NNReal) : ENNReal) := by
      rw [ENNReal.coe_div (by norm_num), ENNReal.coe_add, ENNReal.coe_div (by norm_num)]; norm_num
    rw [h1, h2, ENNReal.coe_inj]
    norm_num

/-- **Completeness of one round.** On non-isomorphic graphs the honest prover always names the
picked graph. -/
private theorem acceptProb_round_prover {x : Graph × Graph} (hx : x ∈ GraphNonIsomorphism) :
    acceptProb (round x) (prover x) = 1 := by
  refine acceptProb_guessingProver fun m hm hm' => hx ?_
  simp only [eval_message] at hm hm'
  obtain ⟨σ, hσ⟩ := exists_equiv_of_mem_support_relabelDist hm hm'
  exact mem_GraphIsomorphism_iff.2 ⟨σ, hσ⟩

/-- One round is an interactive proof for `GraphNonIsomorphism` with completeness `1` and
soundness error `17 / 32`. -/
theorem isInteractiveProof_round :
    IsInteractiveProof round GraphNonIsomorphism 1 (17 / 32) where
  complete x hx := ⟨prover x, (acceptProb_round_prover hx).ge⟩
  sound _ hx P := acceptProb_round_le (not_not.1 hx) P

/-- **Completeness.** On non-isomorphic graphs the honest prover passes both rounds. -/
theorem acceptProb_verifier_prover {x : Graph × Graph} (hx : x ∈ GraphNonIsomorphism) :
    acceptProb (verifier x) (prover x) = 1 :=
  le_antisymm (PMF.coe_le_one _ _) (le_of_eq_of_le (one_pow 2).symm
    (le_acceptProb_sequentialRepeat (prover x) (fun _ => (acceptProb_round_prover hx).ge) 2))

/-- **Soundness.** On isomorphic graphs every prover passes both rounds with probability at most
`(17 / 32) ^ 2`. -/
theorem acceptProb_verifier_le {x : Graph × Graph} (hx : x ∈ GraphIsomorphism) (P : Prover Unit) :
    acceptProb (verifier x) P ≤ (17 / 32) ^ 2 :=
  acceptProb_sequentialRepeat_le (acceptProb_round_le hx) 2 P

/-- The verifier, two sequential rounds, is an interactive proof for `GraphNonIsomorphism` with
completeness `1` and soundness error `(17 / 32) ^ 2`. -/
theorem isInteractiveProof_verifier :
    IsInteractiveProof verifier GraphNonIsomorphism 1 ((17 / 32) ^ 2) where
  complete x hx := ⟨prover x, (acceptProb_verifier_prover hx).ge⟩
  sound _ hx := acceptProb_verifier_le (not_not.1 hx)

/-- Relabeling a computed graph by random keys is strict PPT. -/
private theorem isPPTOn_relabelMessage {γ : Type} {input : γ ↪ List Bool} {G : γ → Graph}
    (hG : ComputableTidilyInPolyTime G input encGraph) :
    IsPPTOn input encBits (fun x => relabelMessage (G x)) := by
  have hn : ComputableTidilyInPolyTime (fun x => (G x).distinctVertices.length) input encUnary :=
    (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.tidy.comp hG)
  have hsize : ComputableTidilyInPolyTime (fun x => 16 * (G x).distinctVertices.length *
      (G x).distinctVertices.length) input encUnary := by fun_prop
  have hw : ComputableTidilyInPolyTime (fun x => keyWidth (G x).distinctVertices.length) input
      encUnary := (unary_clog_const 2).comp hsize
  have hpow : ComputableTidilyInPolyTime (fun x => 2 ^ keyWidth (G x).distinctVertices.length)
      input encUnary := unary_pow_clog_const hsize 2 2
  have hcount : ComputableTidilyInPolyTime (fun x => (G x).distinctVertices.length *
      keyWidth (G x).distinctVertices.length) input encUnary := by fun_prop
  have hkeys : ComputableTidilyInPolyTime (fun p : γ × List Bool =>
      keysOf (G p.1).distinctVertices.length (keyWidth (G p.1).distinctVertices.length) p.2)
      (encPair input encBits) (encList encUnary) :=
    mapWithInput (bitsRowsWithInput (hn.comp (fst input encBits)) (hw.comp (fst input encBits))
      (snd input encBits))
      (bitsBoundedBinaryValueWithInput (hpow.comp ((fst input encBits).comp
        (fst (encPair input encBits) encBits))) (snd (encPair input encBits) encBits))
  exact IsPPTOn.map_with (f := fun x bits => relabel (G x) (keysOf (G x).distinctVertices.length
    (keyWidth (G x).distinctVertices.length) bits)) hcount.sampleList
    (computableInPolyTime_relabel (.of_tidy (hG.comp (fst input encBits))) (.of_tidy hkeys))

/-- The verifier is strict oracle PPT. -/
theorem isOraclePPTOn_verifier :
    IsOraclePPTOn (encPair encGraph encGraph) encBool verifier := by
  have hmessage : IsPPTOn (encPair (encPair encGraph encGraph) encBool) encBits
      (fun p => message p.1 p.2) :=
    isPPTOn_relabelMessage (G := fun p : (Graph × Graph) × Bool => if p.2 then p.1.2 else p.1.1)
      (by fun_prop)
  exact isOraclePPTOn_sequentialRepeat (isOraclePPTOn_guessingRound hmessage) 2

/-- **Graph non-isomorphism has an interactive proof**, with perfect completeness. -/
theorem mem_IP : GraphNonIsomorphism ∈ IP (encPair encGraph encGraph) := by
  refine mem_IP_of isOraclePPTOn_verifier isInteractiveProof_verifier
    (ENNReal.div_le_of_le_mul (by norm_num)) ?_
  have h1 : ((17 : ENNReal) / 32) = ((17 / 32 : NNReal) : ENNReal) := by
    rw [ENNReal.coe_div (by norm_num)]; norm_num
  have h2 : (1 : ENNReal) / 3 = ((1 / 3 : NNReal) : ENNReal) := by
    rw [ENNReal.coe_div (by norm_num)]; norm_num
  rw [h1, h2, ← ENNReal.coe_pow, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  norm_num

end GraphNonIsomorphism

end Cslib.Complexity
