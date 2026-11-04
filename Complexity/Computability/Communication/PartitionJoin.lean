/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Rank
public import Complexity.Foundations.Combinatorics.SetPartition.JoinMatrix

/-!
# Communication complexity of joining partitions

Alice and Bob each hold a partition of a finite nonempty type `α`, and want to decide whether the
join of their partitions is the partition with one block; equivalently, whether the union of a graph
whose components are Alice's blocks and one whose components are Bob's blocks is connected. The
communication matrix of this function is the join matrix of the partition lattice, which has full
rank (`Cslib.SetPartition.rank_joinMatrix`), so by the rank bound every deterministic protocol
sends at least `⌈log₂ B⌉` bits, where `B` is the number of partitions of `α`
(`clog_card_le_ecomplexity_join`). The same holds for the negation, whether the join has more than
one block (`clog_card_le_ecomplexity_join_ne`).

## Main results

* `Cslib.Communication.clog_card_le_ecomplexity_join`: `⌈log₂ B⌉ ≤ D` for `P ⊔ Q = ⊤`.
* `Cslib.Communication.clog_card_le_ecomplexity_join_ne`: `⌈log₂ B⌉ ≤ D` for `P ⊔ Q ≠ ⊤`.

This is the deterministic lower bound for graph connectivity in the framework of Lovász and Saks,
where the join matrix is the span indicator of the graphic matroid of a complete graph and its rank
is computed from the Möbius function [LovaszSaks1993, Theorems 3.6 and 6.3].

## References

* [T. A. Dowling and R. M. Wilson, *Whitney number inequalities for geometric
  lattices*][DowlingWilson1975]
* [L. Lovász and M. Saks, *Communication complexity and combinatorial lattice
  theory*][LovaszSaks1993]
-/

public section

namespace Cslib.Communication

open Cslib.SetPartition

variable {α : Type*} [Finite α] [Nonempty α]

omit [Finite α] [Nonempty α] in
open Classical in
/-- The communication matrix of joining partitions to one block is the join matrix. -/
theorem communicationMatrix_join :
    communicationMatrix ℚ (fun P Q : Setoid α => decide (P ⊔ Q = ⊤)) = joinMatrix α := by
  ext P Q
  simp

open Classical in
/-- A protocol computing a function `f` whose value, or its negation, is `P ⊔ Q = ⊤` sends at
least `⌈log₂ B⌉` bits. -/
private theorem clog_card_le_depth {f : Setoid α → Setoid α → Bool} (g : Bool → Bool)
    (hg : ∀ P Q, g (f P Q) = decide (P ⊔ Q = ⊤)) {p : Protocol (Setoid α) (Setoid α) Bool}
    (hp : p.run = f) : Nat.clog 2 (Fintype.card (Setoid α)) ≤ p.depth := by
  have h := Protocol.rank_communicationMatrix_comp_le (R := ℚ) hp g
  have e : (fun P Q => g (f P Q)) = fun P Q : Setoid α => decide (P ⊔ Q = ⊤) :=
    funext₂ hg
  rw [e, communicationMatrix_join, rank_joinMatrix] at h
  refine Nat.clog_le_of_le_pow (h.trans ?_)
  exact (Finset.card_le_univ _).trans ((Finset.card_univ.trans (Fintype.card_fin _)).le.trans
    p.leafCount_le_two_pow_depth)

open Classical in
/-- **Joining partitions to one block** needs `⌈log₂ B⌉` bits, for `B` the number of partitions. -/
theorem clog_card_le_ecomplexity_join :
    (Nat.clog 2 (Fintype.card (Setoid α)) : ℕ∞) ≤
      Protocol.ecomplexity (fun P Q : Setoid α => fun b => decide (P ⊔ Q = ⊤) = b)
        Set.univ Set.univ :=
  Protocol.le_ecomplexity_iff.mpr fun _ hp => by
    exact_mod_cast clog_card_le_depth (α := α) id (fun _ _ => rfl) (Protocol.solves_univ_iff.mp hp)

open Classical in
/-- **Separating partitions**, deciding whether their join has more than one block, needs
`⌈log₂ B⌉` bits, for `B` the number of partitions. -/
theorem clog_card_le_ecomplexity_join_ne :
    (Nat.clog 2 (Fintype.card (Setoid α)) : ℕ∞) ≤
      Protocol.ecomplexity (fun P Q : Setoid α => fun b => decide (P ⊔ Q ≠ ⊤) = b)
        Set.univ Set.univ :=
  Protocol.le_ecomplexity_iff.mpr fun _ hp => by
    exact_mod_cast clog_card_le_depth (α := α) not (fun _ _ => by simp)
      (Protocol.solves_univ_iff.mp hp)

end Cslib.Communication
