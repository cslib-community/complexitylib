/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Byzantine.NodeBound
public import CslibFrontier.Foundations.Data.BitString.MajorityVote

/-!
# Byzantine agreement against one fault

The protocol `om1` solves Byzantine agreement against one Byzantine fault among `n ≥ 4`
processes in two rounds. In round 1 every process sends its input to everyone; in round 2 every
process relays everything it received. Process `i` then estimates the input of each `k` as the
strict majority `w k` of the `n - 1` relays from the processes `j ≠ k` of what `k` sent them,
and decides the strict majority of `w`, ties going to `false`.

With at most one fault, a correct `k` is reported correctly by at least `n - 2 > (n - 1) / 2`
relays, so every correct process computes `w k = x k`; a faulty `k` is relayed only by correct
processes, so all correct processes compute the same `w k`. Agreement follows, and validity because
at least `n - 1 > n / 2` entries of `w` are correct inputs. This is the single-fault procedure of
[Pease, Shostak and Lamport, §2][PeaseShostakLamport1980] (there for `n = 4`), generalized to
`n ≥ 4` and followed by a majority vote, as in the oral messages algorithm `OM(1)`
[Lamport, Shostak and Pease, §3, Theorem 1][LamportShostakPease1982], except that a process
estimates its own input from the relays as it does every other.

Together with the node bound this settles the single-fault case:
`exists_solvesByzantineAgreement_one_iff` says that `n` processes can solve Byzantine agreement
against one fault in `R ≥ 2` rounds exactly when `n ≤ 1` or `n ≥ 4`. The recursive algorithm
`OM(t)` for any number of faults, and the proof that `om1` decides as its case `t = 1`, are in
`CslibFrontier.Computability.Distributed.Byzantine.RecursiveOralMessages`.

## Main definitions

* `Cslib.Distributed.Byzantine.om1`: two-round agreement against one fault.

## Main results

* `Cslib.Distributed.Byzantine.solvesByzantineAgreement_om1`: `om1` tolerates one fault among
  `n ≥ 4` processes in any `R ≥ 2` rounds.
* `Cslib.Distributed.Byzantine.exists_solvesByzantineAgreement_one_iff`: the single-fault case
  is solvable exactly when `n ≤ 1` or `n ≥ 4`.

## References

* [M. Pease, R. Shostak, L. Lamport, *Reaching agreement in the presence of
  faults*][PeaseShostakLamport1980]
* [L. Lamport, R. Shostak, M. Pease, *The Byzantine generals problem*][LamportShostakPease1982]
-/

public section

namespace Cslib.Distributed.Byzantine

open Finset BitString

/-- The local state of a process running `om1`. -/
structure OM1State (P : Type*) where
  /-- The process's own input. -/
  input : Bool
  /-- `heard j`: the bit received from `j` in round 1. -/
  heard : P → Bool
  /-- `report j k`: the bit that `j` claimed in round 2 to have received from `k` in round 1. -/
  report : P → P → Bool

/-- Two-round Byzantine agreement against one fault. Round 1 sends the input to everyone, round 2
relays the bits received in round 1, and later rounds change nothing. The decision is the strict
majority over `k` of the strict majority `w k` of the relays `report j k` by the processes
`j ≠ k`, ties going to `false`. -/
@[expose] def om1 (P : Type*) [Fintype P] [DecidableEq P] :
    Protocol P (OM1State P) (P → Bool) where
  init _ b := ⟨b, fun _ => b, fun _ _ => b⟩
  send r _ s _ := match r with
    | 0 => fun _ => s.input
    | _ + 1 => s.heard
  update r i s m := match r with
    | 0 => { s with heard := fun j => m j i }
    | 1 => { s with report := m }
    | _ + 2 => s
  output _ s := strictMajorityOn univ fun k =>
    strictMajorityOn (univ.erase k) fun j => s.report j k

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- `om1` changes nothing after round 2. -/
theorem om1_state_add_two (F : Finset P) (adv : ℕ → P → P → P → Bool) (x : P → Bool) (i : P) :
    ∀ r, (om1 P).state F adv x (r + 2) i = (om1 P).state F adv x 2 i
  | 0 => rfl
  | r + 1 => by
    rw [← om1_state_add_two F adv x i r]
    rfl

private theorem om1_heard (F : Finset P) (adv : ℕ → P → P → P → Bool) (x : P → Bool)
    (i j : P) (hj : j ∉ F) : ((om1 P).state F adv x 1 i).heard j = x j := by
  simp only [Protocol.state, om1, hj, ite_false]

private theorem om1_report (F : Finset P) (adv : ℕ → P → P → P → Bool) (x : P → Bool)
    (i j k : P) (hj : j ∉ F) :
    ((om1 P).state F adv x 2 i).report j k = ((om1 P).state F adv x 1 j).heard k := by
  simp only [Protocol.state, om1, hj, ite_false]

/-- **Oral messages against one fault**: `om1` solves Byzantine agreement against one fault among
`n ≥ 4` processes in any `R ≥ 2` rounds. It is the single-fault procedure of
[Pease, Shostak and Lamport, §2][PeaseShostakLamport1980] (there for `n = 4`), generalized to
`n ≥ 4`, followed by the majority vote of `OM(1)`
[Lamport, Shostak and Pease, Theorem 1][LamportShostakPease1982]. -/
theorem solvesByzantineAgreement_om1 (hn : 4 ≤ Fintype.card P) {R : ℕ} (hR : 2 ≤ R) :
    (om1 P).SolvesByzantineAgreement 1 R := by
  obtain ⟨R, rfl⟩ := Nat.exists_eq_add_of_le' hR
  -- A correct process estimates the input of a correct `k` correctly.
  have hw : ∀ (F : Finset P), F.card ≤ 1 → ∀ adv x, ∀ i ∉ F, ∀ k ∉ F,
      strictMajorityOn (univ.erase k) (fun j => ((om1 P).state F adv x 2 i).report j k) =
        x k := by
    intro F hF adv x i hi k hk
    refine strictMajorityOn_eq_of_forall_notMem (F := F) (fun j _ hj => ?_) ?_
    · rw [om1_report F adv x i j k hj, om1_heard F adv x j k hk]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
      omega
  have hdec : ∀ (F : Finset P) adv x i, (om1 P).decision F adv x (R + 2) i =
      strictMajorityOn univ fun k =>
        strictMajorityOn (univ.erase k) fun j => ((om1 P).state F adv x 2 i).report j k := by
    intro F adv x i
    rw [Protocol.decision, om1_state_add_two]
    rfl
  constructor
  · intro F hF adv x i hi i' hi'
    rw [hdec, hdec]
    congr 1 with k : 1
    by_cases hk : k ∈ F
    · -- A faulty `k` is relayed only by correct processes, identically to everyone.
      refine strictMajorityOn_congr fun j hj => ?_
      have hjF : j ∉ F := fun hjF =>
        Finset.ne_of_mem_erase hj (Finset.card_le_one.1 hF j hjF k hk)
      rw [om1_report F adv x i j k hjF, om1_report F adv x i' j k hjF]
    · rw [hw F hF adv x i hi k hk, hw F hF adv x i' hi' k hk]
  · intro F hF adv x v hv i hi
    rw [hdec]
    refine strictMajorityOn_eq_of_forall_notMem (F := F) (fun k _ hk => ?_) ?_
    · rw [hw F hF adv x i hi k hk, hv k hk]
    · rw [Finset.card_univ]
      omega

/-- **The single-fault case.** For `R ≥ 2`, some protocol on `n` processes solves Byzantine
agreement against one fault in `R` rounds exactly when `n ≤ 1` or `n ≥ 4`: `ownInput` and `om1`
solve it, and the node bound
[Fischer, Lynch and Merritt, Theorem 1][FischerLynchMerritt1985] excludes `n = 2, 3`. -/
theorem exists_solvesByzantineAgreement_one_iff (n : ℕ) {R : ℕ} (hR : 2 ≤ R) :
    (∃ (S M : Type) (π : Protocol (Fin n) S M), π.SolvesByzantineAgreement 1 R) ↔
      n ≤ 1 ∨ 4 ≤ n := by
  constructor
  · rintro ⟨S, M, π, h⟩
    by_contra hn
    exact π.not_solvesByzantineAgreement (by simp only [Fintype.card_fin]; omega)
      (by simp only [Fintype.card_fin]; omega) h
  · rintro (hn | hn)
    · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 hn
      exact ⟨_, _, _, Protocol.solvesByzantineAgreement_ownInput 1 R⟩
    · exact ⟨_, _, _, solvesByzantineAgreement_om1 (by simp only [Fintype.card_fin]; omega) hR⟩

end Cslib.Distributed.Byzantine
