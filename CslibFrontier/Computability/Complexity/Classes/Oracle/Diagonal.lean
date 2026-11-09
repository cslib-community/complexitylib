/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Foundations.Data.BitString.ShortWords
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# An oracle diagonalizing against query-bounded deterministic programs

Consider countably many families `D i` of deterministic word-query programs, where `D i n` makes
fewer than `2 ^ n` requests for all large `n`, against every oracle. Then some oracle language `B`
defeats every family on the question whether `B` has a word of length `n`: for each `i` there is
an `n` at which `D i n`, run against `B`, does not answer it
(`Cslib.Complexity.exists_oracle_diagonal`). This is the combinatorial core of the theorem of
Baker, Gill and Solovay [Arora and Barak, Theorem 3.7][AroraBarak09].

The oracle is built in stages along an enumeration of the families. Every stage has decided the
words up to some length. The next stage chooses a length `n` beyond it at which the family makes
fewer than `2 ^ n` requests, runs the family against the words decided so far (all others
answered negatively), and adds an unrequested word of length `n` exactly when the family answers
negatively. It then decides every word up to the longest request. Later stages add only longer
words, so by locality (`Cslib.OracleComp.interpret_id_congr`) the final oracle receives the same
requests and the same answer as at that stage.

The construction uses choice and is not claimed to be computable. Its counting step uses
`Cslib.BitString.exists_length_eq_notMem` from the binary-word API.

## Main results

* `Cslib.Complexity.exists_oracle_diagonal`: one oracle defeats every query-bounded family.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

variable {Operation : Type}

/-- One stage defeats `D`. It extends an approximation `S`, whose words have length at most `m`,
only by words longer than `m`, and decides every word up to a new length `m'`: any oracle agreeing
with the extension up to length `m'` is defeated at some `n`. -/
private theorem stage {D : ℕ → WordQueryComp Operation Bool} {bound : ℕ → ℕ}
    (hbound : ∀ᶠ n in Filter.atTop, bound n < 2 ^ n)
    (hqueries : ∀ n (A : Set (List Bool)),
      (OracleComp.queriesWith (languageOracle A) (D n)).length ≤ bound n)
    (S : Set (List Bool)) (m : ℕ) (hS : ∀ w ∈ S, w.length ≤ m) :
    ∃ (m' : ℕ) (S' : Set (List Bool)), m < m' ∧ S ⊆ S' ∧ (∀ w ∈ S', w.length ≤ m') ∧
      (∀ w ∈ S', w.length ≤ m → w ∈ S) ∧
      ∃ n, ∀ B : Set (List Bool), (∀ w, w.length ≤ m' → (w ∈ B ↔ w ∈ S')) →
        ¬(OracleComp.interpret (m := Id) (languageOracle B) (D n) = true ↔
          ∃ w ∈ B, w.length = n) := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbound
  set n := max N (m + 1) with hn
  have hmn : m < n := by omega
  set Q := (OracleComp.queriesWith (languageOracle S) (D n)).map Prod.snd with hQ
  have hQlen : Q.length < 2 ^ n := by
    rw [hQ, List.length_map]
    exact (hqueries n S).trans_lt (hN n (le_max_left _ _))
  set m' := n + (Q.map List.length).sum with hm'
  have hQm' : ∀ w ∈ Q, w.length ≤ m' := fun w hw =>
    (List.le_sum_of_mem (List.mem_map_of_mem hw)).trans (Nat.le_add_left _ _)
  obtain ⟨w, hwn, hwQ⟩ := BitString.exists_length_eq_notMem Q n hQlen
  -- add an unrequested word of length `n` exactly when `D n` answers negatively against `S`
  set S' : Set (List Bool) :=
    if OracleComp.interpret (m := Id) (languageOracle S) (D n) = true then S else insert w S
  have hSS' : S ⊆ S' := by
    simp only [S']; split_ifs
    · exact le_rfl
    · exact Set.subset_insert _ _
  have hS'm' : ∀ v ∈ S', v.length ≤ m' := by
    intro v hv
    simp only [S'] at hv; split_ifs at hv
    · exact (hS v hv).trans (by omega)
    · rcases hv with rfl | hv
      · omega
      · exact (hS v hv).trans (by omega)
  have hS'old : ∀ v ∈ S', v.length ≤ m → v ∈ S := by
    intro v hv hvm
    simp only [S'] at hv; split_ifs at hv
    · exact hv
    · rcases hv with rfl | hv
      · omega
      · exact hv
  refine ⟨m', S', by omega, hSS', hS'm', hS'old, n, fun B hB => ?_⟩
  -- `B` answers every request of the stage as `S` does
  have hagree : ∀ q ∈ OracleComp.queriesWith (languageOracle S) (D n), q.2 ∈ B ↔ q.2 ∈ S := by
    intro q hq
    have hqQ : q.2 ∈ Q := List.mem_map_of_mem hq
    rw [hB _ (hQm' _ hqQ)]
    simp only [S']; split_ifs
    · exact Iff.rfl
    · exact ⟨fun h => h.resolve_left fun h' => hwQ (h' ▸ hqQ), Or.inr⟩
  rw [(interpret_languageOracle_congr (D n) hagree).1]
  -- whether `B` has a word of length `n` is decided by `S'`
  have hlen : (∃ v ∈ B, v.length = n) ↔ ∃ v ∈ S', v.length = n := by
    constructor
    · rintro ⟨v, hv, hvn⟩
      exact ⟨v, (hB v (by omega)).mp hv, hvn⟩
    · rintro ⟨v, hv, hvn⟩
      exact ⟨v, (hB v (by omega)).mpr hv, hvn⟩
  rw [hlen]
  by_cases hacc : OracleComp.interpret (m := Id) (languageOracle S) (D n) = true
  · -- a positive answer: no word of length `n` is added, and `S` has none
    have hnone : ¬∃ v ∈ S', v.length = n := by
      rintro ⟨v, hv, hvn⟩
      simp only [S', hacc, ite_true] at hv
      exact absurd (hS v hv) (by omega)
    exact fun h => hnone (h.mp hacc)
  · -- a negative answer: the unrequested word of length `n` is added
    have hsome : ∃ v ∈ S', v.length = n := ⟨w, by simp [S', hacc], hwn⟩
    exact fun h => hacc (h.mpr hsome)

/-- **An oracle defeating every query-bounded family.** Given countably many families of
deterministic word-query programs, where `D i n` makes at most `bound i n` requests against every
oracle language and `bound i n < 2 ^ n` for all large `n`, some oracle language `B` defeats each
family: for every `i` there is an `n` at which `D i n`, run against `B`, does not answer whether
`B` has a word of length `n`. -/
theorem exists_oracle_diagonal {ι : Type} [Countable ι]
    (D : ι → ℕ → WordQueryComp Operation Bool) (bound : ι → ℕ → ℕ)
    (hbound : ∀ i, ∀ᶠ n in Filter.atTop, bound i n < 2 ^ n)
    (hqueries : ∀ i n (A : Set (List Bool)),
      (OracleComp.queriesWith (languageOracle A) (D i n)).length ≤ bound i n) :
    ∃ B : Set (List Bool), ∀ i, ∃ n,
      ¬(OracleComp.interpret (m := Id) (languageOracle B) (D i n) = true ↔
        ∃ w ∈ B, w.length = n) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun i => isEmptyElim i⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  -- a stage is an approximation with a bound on the lengths of its words
  let Data := {p : Set (List Bool) × ℕ // ∀ w ∈ p.1, w.length ≤ p.2}
  have hstep (k : ℕ) (p : Data) := stage (hbound (e k)) (hqueries (e k)) p.1.1 p.1.2 p.2
  let next (k : ℕ) (p : Data) : Data :=
    ⟨((hstep k p).choose_spec.choose, (hstep k p).choose),
      (hstep k p).choose_spec.choose_spec.2.2.1⟩
  let seq : ℕ → Data := fun k => Nat.rec ⟨(∅, 0), by simp⟩ next k
  have hseq (k : ℕ) : seq (k + 1) = next k (seq k) := rfl
  -- each stage only adds words longer than the previous bound
  have hmono (k : ℕ) : (seq k).1.2 < (seq (k + 1)).1.2 ∧ (seq k).1.1 ⊆ (seq (k + 1)).1.1 ∧
      ∀ w ∈ (seq (k + 1)).1.1, w.length ≤ (seq k).1.2 → w ∈ (seq k).1.1 := by
    rw [hseq]
    obtain ⟨h₁, h₂, -, h₄, -⟩ := (hstep k (seq k)).choose_spec.choose_spec
    exact ⟨h₁, h₂, h₄⟩
  have hbound_mono : StrictMono fun k => (seq k).1.2 :=
    strictMono_nat_of_lt_succ fun k => (hmono k).1
  have hsub_mono : Monotone fun k => (seq k).1.1 := monotone_nat_of_le_succ fun k => (hmono k).2.1
  -- later stages agree with stage `k` up to its bound
  have hstable (k j : ℕ) (hkj : k ≤ j) (w : List Bool) (hw : w.length ≤ (seq k).1.2) :
      w ∈ (seq j).1.1 ↔ w ∈ (seq k).1.1 := by
    induction j, hkj using Nat.le_induction with
    | base => exact Iff.rfl
    | succ j hkj ih =>
      exact ⟨fun h => ih.mp ((hmono j).2.2 w h (hw.trans (hbound_mono.monotone hkj))),
        fun h => (hmono j).2.1 (ih.mpr h)⟩
  refine ⟨⋃ k, (seq k).1.1, fun i => ?_⟩
  obtain ⟨k, rfl⟩ := he i
  obtain ⟨-, -, -, -, n, hn⟩ := (hstep k (seq k)).choose_spec.choose_spec
  refine ⟨n, hn _ fun w hw => ?_⟩
  change w.length ≤ (seq (k + 1)).1.2 at hw
  change w ∈ ⋃ j, (seq j).1.1 ↔ w ∈ (seq (k + 1)).1.1
  refine ⟨fun h => ?_, fun h => Set.mem_iUnion.mpr ⟨k + 1, h⟩⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
  rcases le_total j (k + 1) with hjk | hkj
  · exact hsub_mono hjk hj
  · exact (hstable (k + 1) j hkj w hw).mp hj

end Cslib.Complexity
