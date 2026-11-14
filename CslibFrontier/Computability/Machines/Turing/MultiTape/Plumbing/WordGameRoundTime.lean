/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameRound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameHeader
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
import Mathlib.Tactic.FinCases

/-!
# Polynomial-time native word-game rounds

One finite machine gathers the selected move and metadata, computes the next control header and
metadata on separate tapes, clears the query, and restores every head. Its polynomial clock
includes gathering, both native computations and their normalization, output writing, cleanup,
and the two real host-input movements. No semantic update is supplied as a free transition.
-/

public section

namespace Turing.MultiTapeTM.WordGameRound

private def projectionTapes {k K : ℕ} (hk : k ≤ K) (dest : Fin 2) :
    Fin (k + 1 + 2) ↪ Fin (K + 4) where
  toFun j := ⟨if j.val < k then j.val else if j.val = k then K + dest.val
    else if j.val = k + 1 then K + 2 else K + 3, by
      have hj := j.isLt
      have hd := dest.isLt
      split_ifs <;> omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hval := congrArg Fin.val h
    have hi := i.isLt
    have hj := j.isLt
    have hd := dest.isLt
    change (if i.val < k then i.val else if i.val = k then K + dest.val
      else if i.val = k + 1 then K + 2 else K + 3) =
      (if j.val < k then j.val else if j.val = k then K + dest.val
      else if j.val = k + 1 then K + 2 else K + 3) at hval
    split_ifs at hval <;> omega

@[simp] private theorem projectionTapes_work {k K : ℕ} (hk : k ≤ K) (dest : Fin 2)
    (i : Fin k) :
    projectionTapes hk dest (i.castSucc.castAdd 2) = (Fin.castLE hk i).castAdd 4 := by
  apply Fin.ext
  change (if i.val < k then i.val else if i.val = k then K + dest.val
    else if i.val = k + 1 then K + 2 else K + 3) = i.val
  simp [i.isLt]

@[simp] private theorem projectionTapes_output {k K : ℕ} (hk : k ≤ K) (dest : Fin 2) :
    projectionTapes hk dest ((Fin.last k).castAdd 2) = Fin.natAdd K (dest.castAdd 2) := by
  apply Fin.ext
  change (if k < k then k else if k = k then K + dest.val
    else if k = k + 1 then K + 2 else K + 3) = K + dest.val
  simp

@[simp] private theorem projectionTapes_input {k K : ℕ} (hk : k ≤ K) (dest : Fin 2) :
    projectionTapes hk dest (Fin.natAdd (k + 1) 0) = Fin.natAdd K 2 := by
  apply Fin.ext
  change (if k + 1 < k then k + 1 else if k + 1 = k then K + dest.val
    else if k + 1 = k + 1 then K + 2 else K + 3) = K + 2
  simp

@[simp] private theorem projectionTapes_marker {k K : ℕ} (hk : k ≤ K) (dest : Fin 2) :
    projectionTapes hk dest (Fin.natAdd (k + 1) 1) = Fin.natAdd K 3 := by
  apply Fin.ext
  change (if k + 2 < k then k + 2 else if k + 2 = k then K + dest.val
    else if k + 2 = k + 1 then K + 2 else K + 3) = K + 3
  simp

private theorem projectionTapes_blank {k K : ℕ} (hk : k ≤ K) (dest : Fin 2)
    (words : Fin 2 → List Bool) (query : List Bool) (hblank : words dest = []) :
    ∀ j ≠ Fin.natAdd (k + 1) 0,
      tapeWords K (words 0) (words 1) query (projectionTapes hk dest j) = [] := by
  intro j hj
  cases j using Fin.addCases with
  | left j =>
    cases j using Fin.lastCases with
    | last =>
      rw [projectionTapes_output]
      fin_cases dest <;> simpa [tapeWords] using hblank
    | cast j => simp [tapeWords]
  | right j =>
    fin_cases j
    · exact (hj rfl).elim
    · simp [tapeWords]

private theorem tapeWords_update (K : ℕ) (words : Fin 2 → List Bool)
    (query result : List Bool) (dest : Fin 2) :
    Function.update (tapeWords K (words 0) (words 1) query)
      (Fin.natAdd K (dest.castAdd 2)) result =
      tapeWords K (Function.update words dest result 0) (Function.update words dest result 1)
        query := by
  funext j
  cases j using Fin.addCases with
  | left j => simp [tapeWords, Function.update_of_ne (Fin.castAdd_ne_natAdd j _)]
  | right j => fin_cases dest <;> fin_cases j <;> simp [tapeWords]

/-- Compile a plain native update into one finite round on the separate control and metadata
words. The common polynomial clock depends only on the current metadata length. -/
theorem exists_round {α : Type} (enc : α ↪ List Bool) (f : Bool × α → Option Bool × α)
    (hf : ComputableInPolyTime f (encPair encBool enc) (encPair (encOption encBool) enc)) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 4) Bool S) (c d : ℕ),
      ∀ (input out : List Bool) (player move : Bool) (a : α),
        tm.runFrom ((config k input [player, move] (enc a) out).withState (some tm.q₀))
          (c * ((enc a).length + 1) ^ d) =
          (config k input (wordGameHeader (f (move, a)).1) (enc (f (move, a)).2) out).withState
            none := by
  have hheader : ComputableInPolyTime (fun x => wordGameHeader (f x).1)
      (encPair encBool enc) encBits :=
    ((ComputableTidilyInPolyTime.of_finite (encA := encOption encBool) (encB := encBits)
      wordGameHeader).comp hf.tidy.fst').computableInPolyTime
  have hmetadata : ComputableInPolyTime (fun x => (f x).2) (encPair encBool enc) enc :=
    hf.tidy.snd'.computableInPolyTime
  obtain ⟨kH, SH, hSH, header, cH, dH, hh⟩ := WordFunction.exists_of_polyTime hheader
  obtain ⟨kM, SM, hSM, metadata, cM, dM, hm⟩ := WordFunction.exists_of_polyTime hmetadata
  let := hSH
  let := hSM
  let K := kH + kM
  let eH := projectionTapes (show kH ≤ K by omega) 0
  let eM := projectionTapes (show kM ≤ K by omega) 1
  let clearQuery := (clearWork Bool).extendTapes (tapeEmb (Fin.natAdd K (2 : Fin 4)))
  let round := ((gatherOn K).seq ((header.extendTapes eH).seq
    ((metadata.extendTapes eM).seq clearQuery))).fromLeftBlank
  let time (n : ℕ) := 6 * n + 23 +
    (cH * (n + 4) ^ dH + (cM * (n + 4) ^ dM + 3 * (n + 4))) + 2
  have htime : Cslib.PolynomiallyBounded time := by unfold time; fun_prop
  obtain ⟨c, d, hbound⟩ := Cslib.polynomiallyBounded_iff_le.mp htime
  refine ⟨K, _, inferInstance, round, c, d, ?_⟩
  intro input out player move a
  let query := [true, move, false] ++ enc a
  let nextHeader := wordGameHeader (f (move, a)).1
  let nextMetadata := enc (f (move, a)).2
  have hquery : (encPair encBool enc) (move, a) = query := by
    simp [encPair_apply, encBool_apply, frame, query]
  have hH := hh (K + 4) eH input (move, a) (tapeWords K [] [] query) out
    (by simp [eH, tapeWords, hquery])
    (projectionTapes_blank _ 0 ![[], []] query rfl)
  have hM := hm (K + 4) eM input (move, a) (tapeWords K nextHeader [] query) out
    (by simp [eM, tapeWords, hquery])
    (projectionTapes_blank _ 1 ![nextHeader, []] query rfl)
  have hclear := RunsBetween.of_transformsTapes (input := input)
    (transformsTapes_clearWork_tapeEmb (Fin.natAdd K 2) query)
    (ws := tapeWords K nextHeader nextMetadata query) (by simp [tapeWords]) 0 out
  obtain ⟨_, _, ⟨rfl, rfl⟩, hclear⟩ := hclear
  have hwH : Function.update (tapeWords K [] [] query) (Fin.natAdd K 0) nextHeader =
      tapeWords K nextHeader [] query := by
    simpa using tapeWords_update K ![[], []] query nextHeader 0
  have hwM : Function.update (tapeWords K nextHeader [] query) (Fin.natAdd K 1) nextMetadata =
      tapeWords K nextHeader nextMetadata query := by
    simpa using tapeWords_update K ![nextHeader, []] query nextMetadata 1
  have hwQ : Function.update (tapeWords K nextHeader nextMetadata query) (Fin.natAdd K 2) [] =
      tapeWords K nextHeader nextMetadata [] := by
    funext j
    cases j using Fin.addCases with
    | left j => simp [tapeWords, Function.update_of_ne (Fin.castAdd_ne_natAdd j _)]
    | right j => fin_cases j <;> simp [tapeWords]
  simp only [eH, projectionTapes_output, encBits_apply, hquery] at hH
  rw [show (0 : Fin 2).castAdd 2 = (0 : Fin 4) from rfl, hwH] at hH
  simp only [eM, projectionTapes_output, hquery] at hM
  rw [show (1 : Fin 2).castAdd 2 = (1 : Fin 4) from rfl, hwM] at hM
  rw [hwQ, List.append_nil] at hclear
  have hr := ((runsBetween_gatherOn K input (enc a) out player move).seq
    (hH.seq (hM.seq hclear))).fromLeftBlank rfl rfl
  have hlength : query.length + 1 = (enc a).length + 4 := by simp [query]
  rw [hlength] at hr
  have hrun : round.runFrom
      ((config K input [player, move] (enc a) out).withState (some round.q₀))
      (time (enc a).length) =
      (config K input nextHeader nextMetadata out).withState none := by
    exact hr.1
  rw [runFrom_eq_of_halt _ _ (hbound (enc a).length) (by rw [hrun]; rfl), hrun]

end Turing.MultiTapeTM.WordGameRound
