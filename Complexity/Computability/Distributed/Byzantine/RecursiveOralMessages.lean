/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Distributed.Byzantine.OralMessages
public import Complexity.Foundations.Data.BitString.MajorityVote

/-!
# Oral messages: Byzantine agreement for `n > 3t`

The oral messages algorithm `OM(m)` of [Lamport, Shostak and Pease, §3][LamportShostakPease1982],
run by every process as commander in parallel, solves Byzantine agreement against `t` faults among
`n > 3t` processes in `t + 1` rounds. With the node bound
(`Complexity.Computability.Distributed.Byzantine.NodeBound`) this gives the exact
characterization `exists_solvesByzantineAgreement_iff`: for `R ≥ t + 1`, `n` processes can solve
Byzantine agreement against `t` faults in `R` rounds exactly when `n ≤ 1` or `n > 3t`.

## The algorithm

`OM(0)`: the commander sends its value to every lieutenant, who uses it. `OM(m + 1)`: the commander
sends its value to every lieutenant; each lieutenant `l` relays the value it received to the other
lieutenants by `OM(m)`; lieutenant `i` takes the strict majority of the value it received from the
commander and the values `OM(m)` gave it for the other lieutenants. Following Lamport, Shostak and
Pease, a recursive instance is named by its *relay path*: the instance at `σ = l :: τ` is the
`OM(·)` instance in which `l` relays the value it obtained in the instance at `τ`, and its
lieutenants are the processes not on `σ`.

`om P t` runs these instances by exponential information gathering. The state of a process is a
tree `List P → Bool`; the entry at the relay path `j :: τ` is written in round `τ.length + 1` with
the entry at `τ` of the tree that `j` sent, and is never changed afterwards. Every process sends its
whole tree every round, so messages are unbounded, as the model allows. After `t + 1` rounds,
`omResolve i (tree of i) t [c]` evaluates `OM(t)` with commander `c` as seen by `i`: at depth `0`
it reads the tree, and at depth `m + 1` it takes the strict majority (ties `false`, the default
order RETREAT) over the processes `l` not on the path of the entry `σ` itself if `l = i`, and of
the value of the subinstance at `l :: σ` otherwise. The decision is the strict majority over all
commanders `c`. As in `om1`, a process also obtains its own input through its own instance; for a
correct process this returns its input.

## Proof

The core results are stated for an arbitrary family of trees `val : P → List P → Bool` that is
*faithful*: a correct `i` holds at `j :: τ` the entry at `τ` of a correct `j`. Runs of `om P t`
give faithful trees (`om_state_cons`, `om_state_freeze`).

* Lemma 1 (`omResolve_eq_of_notMem`): if the commander `j` of the instance at `j :: τ` is correct,
  at most `k` processes off `τ` are faulty and more than `2k + m` processes are off `τ`, then every
  correct process obtains `val j τ` by `OM(m)`.
* Theorem 1 (`omResolve_eq_omResolve`): if `j ∉ τ`, at most `m` processes off `τ` are faulty and
  more than `3m` processes are off `τ`, then all correct processes obtain the same value by
  `OM(m)`.

At the top level `τ = []`: the processes off `τ` are all `n` processes, the generals of the
instance of commander `c`.

## Main definitions

* `Cslib.Distributed.Byzantine.omResolve`: the value of `OM(m)` at a relay path, read from a tree.
* `Cslib.Distributed.Byzantine.om`: `OM(t)` by every process in parallel, by exponential
  information gathering.
* `Cslib.Distributed.Byzantine.omValue`: the value process `i` obtains for the input of `c` by
  `OM(m)` after `R` rounds.
* `Cslib.Distributed.Byzantine.om1Adv`: the faulty messages of a run of `om1`, replayed in
  `om P 1`.

## Main results

* `Cslib.Distributed.Byzantine.omResolve_eq_of_notMem`,
  `Cslib.Distributed.Byzantine.omResolve_eq_omResolve`: Lemma 1 and Theorem 1 for faithful trees.
* `Cslib.Distributed.Byzantine.omValue_eq_of_notMem`: Lemma 1 (IC2) for `OM(m)` in a run of
  `om`, with more than `2k + m` processes and at most `k` faults.
* `Cslib.Distributed.Byzantine.omValue_eq_omValue`: Theorem 1 (IC1) for `OM(m)` in a run of `om`,
  with more than `3m` processes and at most `m` faults.
* `Cslib.Distributed.Byzantine.om_decision_eq_decision_succ`: `om P t` decides in round `t + 1`.
* `Cslib.Distributed.Byzantine.solvesByzantineAgreement_om`: `om P t` solves Byzantine agreement
  against `t` faults among `n > 3t` processes in any `R ≥ t + 1` rounds.
* `Cslib.Distributed.Byzantine.exists_solvesByzantineAgreement_iff`: for `R ≥ t + 1`, Byzantine
  agreement against `t` faults is solvable on `n` processes exactly when `n ≤ 1` or `n > 3t`.
* `Cslib.Distributed.Byzantine.om1_decision_eq_om_decision`: `om1` decides as `om P 1`.

## References

* [L. Lamport, R. Shostak, M. Pease, *The Byzantine generals problem*][LamportShostakPease1982]
* [M. Pease, R. Shostak, L. Lamport, *Reaching agreement in the presence of
  faults*][PeaseShostakLamport1980]
-/

public section

namespace Cslib.Distributed.Byzantine

open Finset BitString

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ### `OM(m)` on a tree -/

/-- `omResolve i val m σ`: the value that process `i`, holding the tree `val`, obtains by `OM(m)`
in the instance at the relay path `σ`, whose commander is the head of `σ` and whose lieutenants
are the processes not on `σ` [Lamport, Shostak and Pease, §3][LamportShostakPease1982]. With
`m = 0` it is the received value `val σ`; with `m + 1` it is the strict majority over the
lieutenants `l` of `val σ` if `l = i` and of the value of `OM(m)` in the instance at `l :: σ`
otherwise. Ties go to `false`. -/
@[expose] def omResolve (i : P) (val : List P → Bool) : ℕ → List P → Bool
  | 0, σ => val σ
  | m + 1, σ => strictMajorityOn σ.toFinsetᶜ fun l =>
      if l = i then val σ else omResolve i val m (l :: σ)

/-- `OM(m)` at `σ` reads only the entries at paths of length at most `σ.length + m`. -/
theorem omResolve_congr (i : P) {val val' : List P → Bool} :
    ∀ (m : ℕ) (σ : List P), (∀ τ : List P, τ.length ≤ σ.length + m → val τ = val' τ) →
      omResolve i val m σ = omResolve i val' m σ
  | 0, σ, h => h σ (by omega)
  | m + 1, σ, h => by
    simp only [omResolve]
    refine strictMajorityOn_congr fun l _ => ?_
    split_ifs
    · exact h σ (by omega)
    · exact omResolve_congr i m (l :: σ) fun τ hτ =>
        h τ (by simp only [List.length_cons] at hτ; omega)

private theorem card_compl_toFinset_cons_le (j : P) (τ : List P) :
    τ.toFinsetᶜ.card ≤ (j :: τ).toFinsetᶜ.card + 1 := by
  rw [Finset.card_compl, Finset.card_compl, List.toFinset_cons]
  have h₁ := Finset.card_insert_le j τ.toFinset
  have h₂ := Finset.card_le_univ (insert j τ.toFinset)
  omega

/-- **Lemma 1 of Lamport, Shostak and Pease**, for faithful trees: `OM(m)` satisfies IC2 when
there are more than `2k + m` generals and at most `k` traitors
[Lamport, Shostak and Pease, §3, Lemma 1][LamportShostakPease1982]. Here the trees `val` are
faithful (`hval`: a correct `i` holds at `j :: τ` the entry at `τ` of a correct `j`), the instance
at `j :: τ` has a correct commander `j`, at most `k` processes off `τ` are faulty and more than
`2k + m` processes are off `τ`. Then every correct process, the commander included, obtains the
value `val j τ` that `j` relays. -/
theorem omResolve_eq_of_notMem {F : Finset P} {val : P → List P → Bool}
    (hval : ∀ i ∉ F, ∀ j ∉ F, ∀ τ, val i (j :: τ) = val j τ) {k : ℕ} :
    ∀ (m : ℕ) (j : P) (τ : List P), j ∉ F → (F \ τ.toFinset).card ≤ k →
      2 * k + m < τ.toFinsetᶜ.card → ∀ i ∉ F, omResolve i (val i) m (j :: τ) = val j τ
  | 0, j, τ, hj, _, _, i, hi => hval i hi j hj τ
  | m + 1, j, τ, hj, hk, hn, i, hi => by
    simp only [omResolve]
    have hcard := card_compl_toFinset_cons_le j τ
    -- The lieutenants off `τ` that are correct vote `val j τ`, and they are a strict majority.
    refine strictMajorityOn_eq_of_forall_notMem (F := F \ τ.toFinset) (fun l hl hlF => ?_) ?_
    · have hlF' : l ∉ F := fun h => hlF (Finset.mem_sdiff.2 ⟨h, fun h' =>
        Finset.mem_compl.1 hl (by rw [List.toFinset_cons]; exact Finset.mem_insert_of_mem h')⟩)
      split_ifs with hli
      · exact hval i hi j hj τ
      · rw [omResolve_eq_of_notMem hval (k := k) m l (j :: τ) hlF' ?_ (by omega) i hi,
          hval l hlF' j hj]
        refine (Finset.card_le_card fun y hy => ?_).trans hk
        simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, not_or] at hy ⊢
        exact ⟨hy.1, hy.2.2⟩
    · omega

/-- **Theorem 1 of Lamport, Shostak and Pease**, for faithful trees: `OM(m)` satisfies IC1 when
there are more than `3m` generals and at most `m` traitors
[Lamport, Shostak and Pease, §3, Theorem 1][LamportShostakPease1982]. Here the trees `val` are
faithful (`hval`), the commander `j` of the instance at `j :: τ` is not on `τ`, at most `m`
processes off `τ` are faulty and more than `3m` processes are off `τ`; the commander may be
faulty. Then all correct processes obtain the same value. (IC2 is `omResolve_eq_of_notMem` with
`k = m`.) -/
theorem omResolve_eq_omResolve {F : Finset P} {val : P → List P → Bool}
    (hval : ∀ i ∉ F, ∀ j ∉ F, ∀ τ, val i (j :: τ) = val j τ) (m : ℕ) :
    ∀ (j : P) (τ : List P), j ∉ τ → (F \ τ.toFinset).card ≤ m →
      3 * m < τ.toFinsetᶜ.card → ∀ p ∉ F, ∀ q ∉ F,
        omResolve p (val p) m (j :: τ) = omResolve q (val q) m (j :: τ) := by
  induction m with
  | zero =>
    intro j τ hjτ hF _ p hp q hq
    by_cases hj : j ∈ F
    · have : j ∈ F \ τ.toFinset := Finset.mem_sdiff.2 ⟨hj, by simpa using hjτ⟩
      exact absurd hF (Nat.not_le.2 (Finset.card_pos.2 ⟨j, this⟩))
    · rw [omResolve_eq_of_notMem hval 0 j τ hj hF (by omega) p hp,
        omResolve_eq_of_notMem hval 0 j τ hj hF (by omega) q hq]
  | succ m ih =>
    intro j τ hjτ hF hn p hp q hq
    by_cases hj : j ∈ F
    · simp only [omResolve]
      have hjτ' : j ∉ τ.toFinset := by simpa using hjτ
      have hcard : τ.toFinsetᶜ.card = (j :: τ).toFinsetᶜ.card + 1 := by
        have := Finset.card_le_univ (insert j τ.toFinset)
        rw [Finset.card_compl, Finset.card_compl, List.toFinset_cons,
          Finset.card_insert_of_notMem hjτ'] at *
        omega
      -- The faulty commander leaves at most `m` faulty processes in the subinstances.
      have hF' : (F \ (j :: τ).toFinset).card ≤ m := by
        have hsub : F \ (j :: τ).toFinset ⊆ (F \ τ.toFinset).erase j := fun y hy => by
          simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, not_or,
            Finset.mem_erase] at hy ⊢
          exact ⟨hy.2.1, hy.1, hy.2.2⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hj, hjτ'⟩)] at this
        omega
      -- A correct lieutenant `l` contributes the value it received, by Lemma 1 for `OM(m)`.
      have hvote : ∀ l ∈ (j :: τ).toFinsetᶜ, l ∉ F → ∀ i ∉ F,
          (if l = i then val i (j :: τ) else omResolve i (val i) m (l :: j :: τ)) =
            val l (j :: τ) := by
        intro l _ hlF i hi
        split_ifs with hli
        · rw [hli]
        · exact omResolve_eq_of_notMem hval m l (j :: τ) hlF hF' (by omega) i hi
      refine strictMajorityOn_congr fun l hl => ?_
      by_cases hlF : l ∈ F
      · -- A faulty lieutenant `l` contributes the same value to all, by Theorem 1 for `OM(m)`.
        have hlp : l ≠ p := fun h => hp (h ▸ hlF)
        have hlq : l ≠ q := fun h => hq (h ▸ hlF)
        simp only [hlp, hlq, ↓reduceIte]
        exact ih l (j :: τ) (by simpa using hl) hF' (by omega) p hp q hq
      · rw [hvote l hl hlF p hp, hvote l hl hlF q hq]
    · rw [omResolve_eq_of_notMem hval (m + 1) j τ hj hF (by omega) p hp,
        omResolve_eq_of_notMem hval (m + 1) j τ hj hF (by omega) q hq]

/-! ### The protocol -/

variable (P) in
/-- `OM(t)` run by every process as commander in parallel, by exponential information gathering
[Lamport, Shostak and Pease, §§1, 3][LamportShostakPease1982]. The state of a process is a tree
`List P → Bool` whose entry at `[]` is its input. Every process sends its tree every round; in
round `r + 1` a process writes, at every path `j :: τ` of length `r + 1`, the entry at `τ` of the
tree received from `j`, and keeps all other entries. The decision is the strict majority, over all
commanders `c`, of the value `omResolve i s t [c]` of `OM(t)` with commander `c`. -/
@[expose] def om (t : ℕ) : Protocol P (List P → Bool) (List P → Bool) where
  init _ b _ := b
  send _ _ s _ := s
  update r _ s msg := fun
    | [] => s []
    | j :: τ => if τ.length = r then msg j τ else s (j :: τ)
  output i s := strictMajorityOn univ fun c => omResolve i s t [c]

/-- The value that process `i` obtains for the input of `c` by `OM(m)` in the run of `om P m`
after `R` rounds. -/
@[expose] def omValue (F : Finset P) (adv : ℕ → P → P → List P → Bool) (x : P → Bool)
    (m R : ℕ) (i c : P) : Bool :=
  omResolve i ((om P m).state F adv x R i) m [c]

variable {t : ℕ} (F : Finset P) (adv : ℕ → P → P → List P → Bool) (x : P → Bool)

/-- The entry at `[]` is the own input. -/
theorem om_state_nil (i : P) : ∀ r, (om P t).state F adv x r i [] = x i
  | 0 => rfl
  | r + 1 => om_state_nil i r

/-- An entry at a path of length `ℓ` does not change after round `ℓ`. -/
theorem om_state_freeze (i : P) (σ : List P) :
    ∀ d, (om P t).state F adv x (σ.length + d) i σ = (om P t).state F adv x σ.length i σ
  | 0 => rfl
  | d + 1 => by
    rw [← om_state_freeze i σ d]
    match σ with
    | [] => rfl
    | j :: τ =>
      change (if τ.length = (j :: τ).length + d then _ else _) = _
      rw [ite_eq_right (by simp only [List.length_cons]; omega)]
      rfl

/-- The entry at `j :: τ` is written in round `τ.length + 1` with what `j` sent: the entry at `τ`
of the tree of `j` if `j` is correct. -/
theorem om_state_cons (i j : P) (τ : List P) :
    (om P t).state F adv x (j :: τ).length i (j :: τ) =
      if j ∈ F then adv τ.length j i τ else (om P t).state F adv x τ.length j τ := by
  change (if τ.length = τ.length then _ else _) = _
  rw [ite_eq_left rfl]
  by_cases hj : j ∈ F
  · simp only [hj, ↓reduceIte]
  · simp only [hj, ↓reduceIte]
    rfl

/-- The tree of frozen entries: the entry of `i` at `σ` after round `σ.length`. -/
private def tree (t : ℕ) (i : P) (σ : List P) : Bool :=
  (om P t).state F adv x σ.length i σ

private theorem tree_cons {i j : P} (hj : j ∉ F) (τ : List P) :
    tree F adv x t i (j :: τ) = tree F adv x t j τ := by
  rw [tree, om_state_cons, ite_eq_right hj]
  rfl

private theorem omResolve_state_eq_tree {m R : ℕ} (hR : m + 1 ≤ R) (i c : P) :
    omResolve i ((om P t).state F adv x R i) m [c] = omResolve i (tree F adv x t i) m [c] := by
  refine omResolve_congr i m [c] fun τ hτ => ?_
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show τ.length ≤ R by
    simp only [List.length_singleton] at hτ; omega)
  rw [hd, om_state_freeze]
  rfl

/-- **Lemma 1 (IC2)** [Lamport, Shostak and Pease, §3, Lemma 1][LamportShostakPease1982]: with
at most `k` faults among more than `2k + m` processes, after `R ≥ m + 1` rounds every correct
process obtains the input of a correct commander `c` by `OM(m)`. -/
theorem omValue_eq_of_notMem {k m R : ℕ} (hF : F.card ≤ k) (hn : 2 * k + m < Fintype.card P)
    (hR : m + 1 ≤ R) {i c : P} (hi : i ∉ F) (hc : c ∉ F) : omValue F adv x m R i c = x c := by
  rw [omValue, omResolve_state_eq_tree F adv x hR,
    omResolve_eq_of_notMem (fun i _ j hj τ => tree_cons F adv x hj τ) m c [] hc
      (by simpa using hF) (by simpa using hn) i hi]
  exact om_state_nil F adv x c 0

/-- **Theorem 1 (IC1)** [Lamport, Shostak and Pease, §3, Theorem 1][LamportShostakPease1982]:
with at most `m` faults among more than `3m` processes, after `R ≥ m + 1` rounds all correct
processes obtain the same value for every commander `c` by `OM(m)`, even when `c` is faulty. -/
theorem omValue_eq_omValue {m R : ℕ} (hF : F.card ≤ m) (hn : 3 * m < Fintype.card P)
    (hR : m + 1 ≤ R) {i j : P} (hi : i ∉ F) (hj : j ∉ F) (c : P) :
    omValue F adv x m R i c = omValue F adv x m R j c := by
  rw [omValue, omValue, omResolve_state_eq_tree F adv x hR, omResolve_state_eq_tree F adv x hR]
  exact omResolve_eq_omResolve (fun i _ j hj τ => tree_cons F adv x hj τ) m c []
    List.not_mem_nil (by simpa using hF) (by simpa using hn) i hi j hj

/-- The decision of `om P t` is the strict majority of the values of `OM(t)`. -/
theorem om_decision (R : ℕ) (i : P) :
    (om P t).decision F adv x R i = strictMajorityOn univ (omValue F adv x t R i) :=
  rfl

/-- `om P t` decides in round `t + 1`: later rounds do not change the decision. -/
theorem om_decision_eq_decision_succ {R : ℕ} (hR : t + 1 ≤ R) (i : P) :
    (om P t).decision F adv x R i = (om P t).decision F adv x (t + 1) i := by
  rw [om_decision, om_decision]
  congr 1
  funext c
  rw [omValue, omValue, omResolve_state_eq_tree F adv x hR,
    omResolve_state_eq_tree F adv x le_rfl]

/-- **Oral messages** [Lamport, Shostak and Pease, §§1, 3][LamportShostakPease1982]: `om P t`
solves Byzantine agreement against `t` faults among `n > 3t` processes in any `R ≥ t + 1`
rounds. Agreement is Theorem 1 (IC1) for every commander, and validity is Lemma 1 (IC2) for the
more than `n / 2` correct commanders. -/
theorem solvesByzantineAgreement_om (hn : 3 * t < Fintype.card P) {R : ℕ} (hR : t + 1 ≤ R) :
    (om P t).SolvesByzantineAgreement t R where
  agreement F hF adv x i hi j hj := by
    rw [om_decision, om_decision]
    congr 1
    funext c
    exact omValue_eq_omValue F adv x hF hn hR hi hj c
  validity F hF adv x v hv i hi := by
    rw [om_decision]
    refine strictMajorityOn_eq_of_forall_notMem (F := F) (fun c _ hc => ?_) ?_
    · rw [omValue_eq_of_notMem F adv x hF (by omega) hR hi hc, hv c hc]
    · rw [Finset.card_univ]
      omega

/-- **Byzantine agreement is solvable exactly when `n ≤ 1` or `n > 3t`.** For `R ≥ t + 1`, some
protocol on `n` processes solves Byzantine agreement against `t` faults in `R` rounds exactly when
`n ≤ 1` or `3t < n`: `Protocol.ownInput` and `om` solve it
[Lamport, Shostak and Pease, Theorem 1][LamportShostakPease1982], and the node bound
[Fischer, Lynch and Merritt, Theorem 1][FischerLynchMerritt1985] excludes `2 ≤ n ≤ 3t`. Whether
fewer than `t + 1` rounds suffice is not addressed here. -/
theorem exists_solvesByzantineAgreement_iff (n t : ℕ) {R : ℕ} (hR : t + 1 ≤ R) :
    (∃ (S M : Type) (π : Protocol (Fin n) S M), π.SolvesByzantineAgreement t R) ↔
      n ≤ 1 ∨ 3 * t < n := by
  constructor
  · rintro ⟨S, M, π, h⟩
    by_contra hn
    exact π.not_solvesByzantineAgreement (by simp only [Fintype.card_fin]; omega)
      (by simp only [Fintype.card_fin]; omega) h
  · rintro (hn | hn)
    · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 hn
      exact ⟨_, _, _, Protocol.solvesByzantineAgreement_ownInput t R⟩
    · exact ⟨_, _, _, solvesByzantineAgreement_om (by simpa using hn) hR⟩

/-! ### `om1` is `OM(1)` -/

/-- The messages of the faulty processes in a run of `om1`, replayed in a run of `om P 1`: the
bit `adv r j i k` that `j` sends to `i` in round `r + 1` about `k` becomes the entry for the relay
path `k :: τ`; in round 1 the path is empty and `adv 0 j i i` is used, as `om1` does. -/
@[expose] def om1Adv (adv : ℕ → P → P → P → Bool) : ℕ → P → P → List P → Bool :=
  fun r j i σ => adv r j i (σ.headD i)

private theorem om_one_state_two (adv : ℕ → P → P → P → Bool) (i : P) :
    (om P 1).state F (om1Adv adv) x 2 i [] = ((om1 P).state F adv x 2 i).input ∧
    (∀ k, (om P 1).state F (om1Adv adv) x 2 i [k] = ((om1 P).state F adv x 2 i).heard k) ∧
    ∀ j k, (om P 1).state F (om1Adv adv) x 2 i [j, k] = ((om1 P).state F adv x 2 i).report j k := by
  have heard : ∀ i k, (om P 1).state F (om1Adv adv) x 1 i [k] =
      ((om1 P).state F adv x 1 i).heard k := by
    intro i k
    by_cases hk : k ∈ F <;> simp [Protocol.state, om, om1, om1Adv, hk]
  refine ⟨rfl, fun k => heard i k, fun j k => ?_⟩
  by_cases hj : j ∈ F
  · simp [Protocol.state, om, om1, om1Adv, hj]
  · have := heard j k
    simp only [Protocol.state, om, om1, hj] at this ⊢
    simpa using this

private theorem om_one_state_eq_two (adv : ℕ → P → P → P → Bool) (R : ℕ) (i : P) (σ : List P)
    (hσ : σ.length ≤ 2) :
    (om P 1).state F (om1Adv adv) x (R + 2) i σ = (om P 1).state F (om1Adv adv) x 2 i σ := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hσ
  rw [show R + 2 = σ.length + (d + R) by omega, om_state_freeze, hd, om_state_freeze]

/-- **`om1` is `OM(1)`**: the single-fault protocol `om1` decides, at every correct process and
after every `R ≥ 2` rounds, as `om P 1` against the replayed faulty messages `om1Adv adv`. -/
theorem om1_decision_eq_om_decision (adv : ℕ → P → P → P → Bool) {R : ℕ} (hR : 2 ≤ R) {i : P}
    (hi : i ∉ F) : (om1 P).decision F adv x R i = (om P 1).decision F (om1Adv adv) x R i := by
  obtain ⟨R, rfl⟩ := Nat.exists_eq_add_of_le' hR
  obtain ⟨-, hheard, hreport⟩ := om_one_state_two F x adv i
  rw [Protocol.decision, om1_state_add_two, om_decision]
  refine strictMajorityOn_congr fun c _ => ?_
  rw [omValue, omResolve_congr i 1 [c] fun τ hτ => om_one_state_eq_two F x adv R i τ hτ]
  have hcompl : [c].toFinsetᶜ = univ.erase c := by
    ext l
    simp only [Finset.mem_compl, List.mem_toFinset, List.mem_singleton, Finset.mem_erase,
      Finset.mem_univ, and_true]
  simp only [omResolve, hcompl]
  refine strictMajorityOn_congr fun l _ => ?_
  rw [← hreport]
  split_ifs with hli
  · -- The relay of `i` to itself is what it heard.
    subst hli
    have hc : (om P 1).state F (om1Adv adv) x 2 l [c] =
        (om P 1).state F (om1Adv adv) x [c].length l [c] := om_state_freeze F (om1Adv adv) x l [c] 1
    rw [hc, ← om_state_cons F (om1Adv adv) x l l [c] |>.trans (ite_eq_right hi)]
    rfl
  · rfl

end Cslib.Distributed.Byzantine
