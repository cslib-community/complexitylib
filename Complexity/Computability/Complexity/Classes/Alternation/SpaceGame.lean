/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Alternation.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Alternating.WordGame
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.StreamFold
import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# Word games on polynomially long positions are in `APSPACE`

A word game (`Turing.MultiTapeATM.WordGame`) whose initial position `I a` and update `U` are
polynomial-time computable, whose reachable positions have polynomial length, and whose plays all
end, is decided in alternating polynomial space: the alternating machine
`Turing.MultiTapeATM.wordGame` keeps only the current position on a work tape, and each round
recomputes the next position in polynomial time and hence polynomial space
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013].

The plays may be exponentially long: only their finiteness is assumed, since deciding asks every
branch to halt. This is the step from deterministic exponential time to `APSPACE`. A game checking
the tableau of a machine running in time `2 ^ n ^ k`, whose positions name one cell of the tableau,
gives `EXP ⊆ APSPACE` with `Cslib.Complexity.APSPACE_subset_EXP`.

## Main results

* `Cslib.Complexity.mem_APSPACE_of_wins`: a word game on polynomially long positions with a
  polynomial-time initial position and update is in `APSPACE`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeATM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Word games on polynomially long positions are in `APSPACE`.** Let the initial position `I a`
and the update `U` be polynomial-time computable, every position reachable from `I a` have length
at most `ℓ a`, polynomial in the instance, and every play from `I a` end. Then the problem of
whether the existential player wins from `I a` is in `APSPACE`. -/
theorem mem_APSPACE_of_wins {A : Set α} {I : α → List Bool} {U : List Bool → List Bool}
    {ℓ : α → ℕ} (hI : ComputableInPolyTime I enc encBits)
    (hU : ComputableInPolyTime U encBits encBits)
    (hℓ : PolyBounded (fun a => (enc a).length) ℓ)
    (hlen : ∀ a w, WordGame.Reach U (I a) w → w.length ≤ ℓ a)
    (hends : ∀ a, ∃ n, WordGame.Ends U n (I a))
    (hA : ∀ a, a ∈ A ↔ WordGame.Wins U (I a)) : A ∈ APSPACE enc := by
  obtain ⟨cI, dI, kI, SI, _, TI, hTI⟩ := Internal.NormalForm.polyTime hI
  obtain ⟨cU, dU, kU, SU, _, TU, hTU⟩ := Internal.NormalForm.polyTime hU
  -- the tapes: the position on `N`, the next position on `O`, a flag on `M`
  set K := kI + kU + 3 with hK
  let N : Fin K := ⟨0, by omega⟩
  let O : Fin K := ⟨1, by omega⟩
  let M : Fin K := ⟨2, by omega⟩
  have hNO : N ≠ O := by simp [N, O]
  have hNM : N ≠ M := by simp [N, M]
  have hOM : O ≠ M := by simp [O, M]
  obtain ⟨eI, heI⟩ := exists_embedding_eq (show kI + 1 ≤ K by omega) (Fin.last kI) N
  obtain ⟨eU, heUi, heUo⟩ := exists_embedding_eq₂ (show kU + 1 + 2 ≤ K by omega)
    (i := Fin.natAdd (kU + 1) 0) (o := (Fin.last kU).castAdd 2) (by simp [Fin.ext_iff]) hNO
  -- the machines
  let Pm := TI.outputToWord.extendTapes eI
  let R := frozenRound (nop K Bool) ((TU.onWords true).extendTapes eU) N O M hNO hNM hOM
  -- the bounds
  let tP : α → ℕ := fun a => cI * ((enc a).length + 1) ^ dI + (I a).length + 2
  let sP : α → ℕ := fun a =>
    cI * ((enc a).length + 1) ^ dI + 2 * (I a).length + kI + 4 + (K - (kI + 1))
  let tR : α → ℕ := fun a => cU * (ℓ a + 1) ^ dU + 10 * ℓ a + 26
  let sR : α → ℕ := fun a => cU * (ℓ a + 1) ^ dU + 10 * ℓ a + 5 * K + 3 * kU + 40
  have hP (a : α) : WordGame.PrepSpec Pm N (enc a) (I a) (tP a) (sP a) := by
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, hsp⟩ := transformsTapes_iff_runFrom.mp
      ((hTI a).outputToWord_onTape heI) (enc a) (fun _ => []) [] ⟨rfl, rfl⟩
    unfold WordGame.PrepSpec
    rw [Cfg.init_eq_wordsCfg]
    exact ⟨hrun, hsp⟩
  have hR (a : α) : WordGame.RoundSpec R N (enc a) U (I a) (tR a) (sR a) := by
    intro u x r hreach b
    have hw : (u :: b :: r).length ≤ ℓ a := by simpa using hlen a _ hreach
    have hUw : (U (u :: b :: r)).length ≤ ℓ a := hlen a _ (WordGame.Reach.move b hreach)
    have hpow : cU * ((u :: b :: r).length + 1) ^ dU ≤ cU * (ℓ a + 1) ^ dU :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have hE := (transformsTapes_nop K Bool).imp
      (P' := fun _ ws => ws = Function.update (fun _ => []) N (u :: b :: r))
      (Q' := fun _ ws ws' em => ws' = ws ∧ em = []) (fun _ _ _ => trivial)
      (fun _ _ _ _ _ h => h) le_rfl le_rfl
    have hNm := (hTU (u :: b :: r)).onWords_extendTapes true heUi heUo
    simp only [encBits_apply] at hNm
    have h := (transformsTapes_frozenRound hNO hNM hOM hE hNm).mono
      (t' := tR a) (s' := sR a) (by simp only [tR]; omega) (by simp only [sR]; omega)
    obtain ⟨ws, em, hrun, ⟨rfl, rfl⟩, hsp⟩ := transformsTapes_iff_runFrom.mp h (enc a) _ [] rfl
    exact ⟨hrun, hsp⟩
  have hspec (a : α) := wordGame_spec (hP a) (hR a)
  refine ⟨K, _, inferInstance, wordGame Pm R N,
    fun a => K * (2 * max (max (sP a) (sR a)) 1 + 1), ?_, ⟨fun a => ⟨(hspec a).1, ?_⟩, fun a => ?_⟩⟩
  · have hlenI : PolyBounded (fun a => (enc a).length) fun a => (I a).length := by
      simpa using hI.polyBounded_length
    have hpowI : PolyBounded (fun a => (enc a).length) fun a => cI * ((enc a).length + 1) ^ dI :=
      PolyBounded.of_forall_le cI dI fun _ => le_rfl
    have hpowU : PolyBounded (fun a => (enc a).length) fun a => cU * (ℓ a + 1) ^ dU :=
      (PolyBounded.of_forall_le (size := id) cU dU fun _ => le_rfl).comp hℓ
    have hsP : PolyBounded (fun a => (enc a).length) sP :=
      (((hpowI.add ((PolyBounded.const 2).mul hlenI)).add (.const kI)).add (.const 4)).add
        (.const _)
    have hsR : PolyBounded (fun a => (enc a).length) sR :=
      (((hpowU.add ((PolyBounded.const 10).mul hℓ)).add (.const _)).add (.const _)).add
        (.const 40)
    refine ((PolyBounded.const K).mul (((PolyBounded.const 2).mul
      ((hsP.add hsR).add (.const 1))).add (.const 1))).mono fun a => ?_
    exact Nat.mul_le_mul_left _ (by omega)
  · rw [hA a, (hspec a).2.1]
  · obtain ⟨n, hn⟩ := hends a
    exact ⟨_, (hspec a).2.2 n hn⟩

end Cslib.Complexity
