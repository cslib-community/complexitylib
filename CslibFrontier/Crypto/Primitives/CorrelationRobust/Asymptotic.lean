/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.CorrelationRobust
public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Probability.BitString.List
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Tactic.PPT

/-!
# Asymptotic Correlation-Robust Hash Families

Word-level probabilistic polynomial-time definitions and security games for correlation-robust
hash families ([IshaiKilianNissimPetrank2003, Definition 1]).

## Main definitions

* `Cslib.Crypto.CorrelationRobust.CorrelationRobustHash`: polynomial-time keyed/tweakable hash
  family parameterized by security parameter `n` and query coordinate `j`.
* `Cslib.Crypto.CorrelationRobust.wordRealSample`, `wordIdealSample`: word-level sampling of
  `(t, H_j(t_j ⊕ s))` vs `(t, u)` for uniformly random `s`, `t`, and `u`.
* `Cslib.Crypto.CorrelationRobust.wordRealGame`, `wordIdealGame`, `IsCorrelationRobust`:
  game-based asymptotic correlation robustness against `WordAdversary.IsPPT` distinguishers.

## Main results

* `Cslib.Crypto.CorrelationRobust.wordAdvantage_eq_finite`: exact equality between the word-level
  game advantage and finite `CorrelationRobust.advantage` at `H.toFinite n`.
* `CorrelationRobustHash.isCorrelationRobust_implies_computationallyIndistinguishable`:
  encoded real and ideal word ensembles are computationally indistinguishable.

## References

* [Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*][IshaiKilianNissimPetrank2003]
-/

public section

namespace Cslib.Crypto.CorrelationRobust

open Cslib.BitString
open Cslib.Probability
open Turing.MultiTapeTM

/-- Bit-string embedding of word-level `(tWords, yWords)` challenge pairs. -/
@[expose] def encWordTuple : (List (List Bool) × List (List Bool)) ↪ List Bool :=
  encPair (encList encBits) (encList encBits)

/-- Bit-string embedding of `(n, (tWords, yWords))` inputs to a correlation-robust adversary. -/
@[expose] def encWordAdvInput : (ℕ × List (List Bool) × List (List Bool)) ↪ List Bool :=
  encPair encUnary encWordTuple

/-- An asymptotic correlation-robust hash family evaluated on word inputs. -/
structure CorrelationRobustHash where
  /-- Number of correlated queries for security parameter `n`. -/
  queries : ℕ → ℕ
  /-- Input secret/query bit-length for security parameter `n`. -/
  keyLength : ℕ → ℕ
  /-- Output bit-length for security parameter `n`. -/
  outLength : ℕ → ℕ
  /-- Deterministic evaluation on security parameter `n`, query index `j`, and key-length word. -/
  eval : ℕ → ℕ → List Bool → List Bool
  /-- Output words have length `outLength n` on valid indices and key-length words. -/
  eval_length :
    ∀ n j x, j < queries n → x.length = keyLength n → (eval n j x).length = outLength n
  /-- The query count is computable in unary polynomial time. -/
  queries_poly : ComputableInPolyTime queries encUnary encUnary
  /-- The key length is computable in unary polynomial time. -/
  keyLength_poly : ComputableInPolyTime keyLength encUnary encUnary
  /-- The output length is computable in unary polynomial time. -/
  outLength_poly : ComputableInPolyTime outLength encUnary encUnary
  /-- Evaluating `eval` is polynomial time in `(n, (j, x))`. -/
  eval_poly : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool => eval p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encBits)) encBits

attribute [fun_prop] CorrelationRobustHash.queries_poly
  CorrelationRobustHash.keyLength_poly
  CorrelationRobustHash.outLength_poly

/-- Evaluating `H.eval` on polynomial-time components is polynomial time. -/
@[fun_prop]
theorem CorrelationRobustHash.eval_polyWithInput (H : CorrelationRobustHash)
    {α : Type} {input : α ↪ List Bool}
    {sec : α → ℕ} {idx : α → ℕ} {word : α → List Bool}
    (hsec : ComputableInPolyTime sec input encUnary)
    (hidx : ComputableInPolyTime idx input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => H.eval (sec a) (idx a) (word a)) input encBits :=
  H.eval_poly.comp (hsec.prod (hidx.prod hword))

/-- `H.queries` applied to a unary polynomial-time input is polynomial time. -/
@[fun_prop]
theorem CorrelationRobustHash.queries_polyWithInput (H : CorrelationRobustHash)
    {α : Type} {input : α ↪ List Bool} {sec : α → ℕ}
    (hsec : ComputableInPolyTime sec input encUnary) :
    ComputableInPolyTime (fun a => H.queries (sec a)) input encUnary :=
  H.queries_poly.comp hsec

/-- `H.keyLength` applied to a unary polynomial-time input is polynomial time. -/
@[fun_prop]
theorem CorrelationRobustHash.keyLength_polyWithInput (H : CorrelationRobustHash)
    {α : Type} {input : α ↪ List Bool} {sec : α → ℕ}
    (hsec : ComputableInPolyTime sec input encUnary) :
    ComputableInPolyTime (fun a => H.keyLength (sec a)) input encUnary :=
  H.keyLength_poly.comp hsec

/-- `H.outLength` applied to a unary polynomial-time input is polynomial time. -/
@[fun_prop]
theorem CorrelationRobustHash.outLength_polyWithInput (H : CorrelationRobustHash)
    {α : Type} {input : α ↪ List Bool} {sec : α → ℕ}
    (hsec : ComputableInPolyTime sec input encUnary) :
    ComputableInPolyTime (fun a => H.outLength (sec a)) input encUnary :=
  H.outLength_poly.comp hsec

/-- Word-level distinguisher for correlation robustness. -/
abbrev WordAdversary := ℕ → List (List Bool) × List (List Bool) → ProbComp Bool

/-- Strict probabilistic polynomial-time admissibility for word-level distinguishers. -/
@[expose] def WordAdversary.IsPPT (adversary : WordAdversary) : Prop :=
  IsPPTOn encWordAdvInput encBool (fun p => adversary p.1 p.2)

/-- Word-level real challenge distribution `(tWords, [H_j(t_j ⊕ s)])`. -/
noncomputable def wordRealSample (H : CorrelationRobustHash) (n : ℕ) :
    ProbComp (List (List Bool) × List (List Bool)) := do
  let s ← BitString.sampleList (H.keyLength n)
  let tFlat ← BitString.sampleList (H.queries n * H.keyLength n)
  let tWords := BitString.listRows (H.queries n) (H.keyLength n) tFlat
  let yWords := (List.range (H.queries n)).map fun j =>
    H.eval n j (BitString.listXor (H.keyLength n)
      [BitString.listRow (H.keyLength n) j tFlat, s])
  return (tWords, yWords)

/-- Word-level ideal challenge distribution `(tWords, uWords)`. -/
noncomputable def wordIdealSample (H : CorrelationRobustHash) (n : ℕ) :
    ProbComp (List (List Bool) × List (List Bool)) := do
  let tFlat ← BitString.sampleList (H.queries n * H.keyLength n)
  let uFlat ← BitString.sampleList (H.queries n * H.outLength n)
  return (BitString.listRows (H.queries n) (H.keyLength n) tFlat,
    BitString.listRows (H.queries n) (H.outLength n) uFlat)

/-- `wordRealSample` runs in strict probabilistic polynomial time. -/
theorem isPPTOn_wordRealSample (H : CorrelationRobustHash) :
    IsPPTOn encUnary encWordTuple (wordRealSample H) := by
  ppt [wordRealSample, encWordTuple]

/-- `wordIdealSample` runs in strict probabilistic polynomial time. -/
theorem isPPTOn_wordIdealSample (H : CorrelationRobustHash) :
    IsPPTOn encUnary encWordTuple (wordIdealSample H) := by
  ppt [wordIdealSample, encWordTuple]

/-- Word-level real game for correlation robustness. -/
@[expose] noncomputable def wordRealGame (H : CorrelationRobustHash) (adversary : WordAdversary)
    (n : ℕ) : Game :=
  ProbComp.eval (wordRealSample H n >>= adversary n)

/-- Word-level ideal game for correlation robustness. -/
@[expose] noncomputable def wordIdealGame (H : CorrelationRobustHash) (adversary : WordAdversary)
    (n : ℕ) : Game :=
  ProbComp.eval (wordIdealSample H n >>= adversary n)

/-- A hash family is correlation-robust if no strict PPT word adversary distinguishes correlated
hash outputs from independent uniform strings with non-negligible advantage. -/
@[expose] def CorrelationRobustHash.IsCorrelationRobust (H : CorrelationRobustHash) : Prop :=
  Game.Indistinguishable (wordRealGame H) (wordIdealGame H) WordAdversary.IsPPT

/-- Fixed-size finite hash view of `H` at security parameter `n`. -/
@[expose] def CorrelationRobustHash.toFinite (H : CorrelationRobustHash) (n : ℕ) :
    Fin (H.queries n) → BitString (H.keyLength n) → BitString (H.outLength n) :=
  fun j x => BitString.ofList (H.outLength n) (H.eval n j.val (List.ofFn x))

/-- Word-list encoding of a finite `(t, y)` challenge pair. -/
@[expose] def encodePair {m k ℓ : ℕ}
    (pair : (Fin m → BitString k) × (Fin m → BitString ℓ)) :
    List (List Bool) × List (List Bool) :=
  (List.ofFn (fun j => List.ofFn (pair.1 j)), List.ofFn (fun j => List.ofFn (pair.2 j)))

/-- Finite correlation-robustness adversary induced by a word-level adversary at parameter `n`. -/
@[expose] def Adversary.ofWord (adversary : WordAdversary) (n m k ℓ : ℕ) :
    Adversary m (BitString k) (BitString ℓ) :=
  fun pair => adversary n (encodePair pair)

private theorem wordRealSample_body_eq (H : CorrelationRobustHash) (n : ℕ)
    (s tFlat : List Bool) :
    (BitString.listRows (H.queries n) (H.keyLength n) tFlat,
      (List.range (H.queries n)).map fun j =>
        H.eval n j (BitString.listXor (H.keyLength n)
          [BitString.listRow (H.keyLength n) j tFlat, s])) =
    encodePair
      (BitString.block (BitString.ofList (H.queries n * H.keyLength n) tFlat),
        fun j : Fin (H.queries n) =>
          H.toFinite n j
            (BitString.block (BitString.ofList (H.queries n * H.keyLength n) tFlat) j +
              BitString.ofList (H.keyLength n) s)) := by
  refine Prod.ext ?_ ?_
  · rw [encodePair, BitString.listRows_eq_ofFn]
  · apply List.ext_getElem (by simp [encodePair])
    intro j hj hj'
    simp only [List.length_map, List.length_range] at hj
    simp only [encodePair, List.getElem_map, List.getElem_range, List.getElem_ofFn,
      CorrelationRobustHash.toFinite]
    have hxor :
        BitString.listXor (H.keyLength n) [BitString.listRow (H.keyLength n) j tFlat, s] =
          List.ofFn
            (BitString.block (BitString.ofList (H.queries n * H.keyLength n) tFlat)
                ⟨j, hj⟩ +
              BitString.ofList (H.keyLength n) s) := by
      rw [BitString.listXor_pair,
        BitString.listRow_eq_ofFn (H.keyLength n) ⟨j, hj⟩ tFlat,
        BitString.ofList_ofFn]
    rw [hxor, BitString.ofFn_ofList (H.eval_length n j _ hj (by simp))]

private theorem bind_map_bind_pure_eq {α α' β β' γ : Type}
    (pa : PMF α) (pb : PMF β) (fa : α → α') (fb : β → β')
    (k : α → β → γ) (k' : α' → β' → γ)
    (h : ∀ a b, k a b = k' (fa a) (fb b)) :
    pa.bind (fun a => pb.bind fun b => PMF.pure (k a b)) =
      (pa.map fa).bind fun a' => (pb.map fb).map (k' a') := by
  rw [PMF.bind_map]
  refine congrArg (PMF.bind pa) (funext fun a => ?_)
  dsimp only [Function.comp_def]
  rw [PMF.map_comp, ← PMF.bind_pure_comp]
  exact congrArg (PMF.bind pb) (funext fun b => congrArg PMF.pure (h a b))

/-- Exact distribution of `wordRealSample` in terms of uniform finite strings and `H.toFinite`. -/
theorem eval_wordRealSample (H : CorrelationRobustHash) (n : ℕ) :
    ProbComp.eval (wordRealSample H n) =
      (PMF.uniformOfFintype (BitString (H.keyLength n))).bind fun s =>
        (PMF.uniformOfFintype (Fin (H.queries n) → BitString (H.keyLength n))).map fun t =>
          encodePair (t, fun j => H.toFinite n j (t j + s)) := by
  rw [← BitString.uniformList_ofList (H.keyLength n),
    ← BitString.uniformList_blocks (H.queries n) (H.keyLength n)]
  simp only [wordRealSample, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  exact bind_map_bind_pure_eq _ _ _ _ _ _ fun s tFlat => wordRealSample_body_eq H n s tFlat

/-- Exact distribution of `wordIdealSample` in terms of independent uniform finite blocks. -/
theorem eval_wordIdealSample (H : CorrelationRobustHash) (n : ℕ) :
    ProbComp.eval (wordIdealSample H n) =
      (PMF.uniformOfFintype (Fin (H.queries n) → BitString (H.keyLength n))).bind fun t =>
        (PMF.uniformOfFintype (Fin (H.queries n) → BitString (H.outLength n))).map fun u =>
          encodePair (t, u) := by
  rw [← BitString.uniformList_blocks (H.queries n) (H.keyLength n),
    ← BitString.uniformList_blocks (H.queries n) (H.outLength n)]
  simp only [wordIdealSample, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  exact bind_map_bind_pure_eq _ _ _ _ _ _ fun tFlat uFlat => by
    simp only [encodePair, BitString.listRows_eq_ofFn]

/-- `wordRealGame` equals finite `CorrelationRobust.realGame` for `H.toFinite n`. -/
theorem wordRealGame_eq_realGame (H : CorrelationRobustHash) (adversary : WordAdversary)
    (n : ℕ) :
    wordRealGame H adversary n =
      realGame (H.toFinite n)
        (Adversary.ofWord adversary n (H.queries n) (H.keyLength n) (H.outLength n)) := by
  rw [wordRealGame, ProbComp.eval_bind, eval_wordRealSample]
  simp only [realGame, ProbComp.eval_bind, ProbComp.eval_uniform, PMF.bind_bind, PMF.bind_map,
    Adversary.ofWord]
  rfl

/-- `wordIdealGame` equals finite `CorrelationRobust.idealGame`. -/
theorem wordIdealGame_eq_idealGame (H : CorrelationRobustHash) (adversary : WordAdversary)
    (n : ℕ) :
    wordIdealGame H adversary n =
      idealGame
        (Adversary.ofWord adversary n (H.queries n) (H.keyLength n) (H.outLength n)) := by
  rw [wordIdealGame, ProbComp.eval_bind, eval_wordIdealSample]
  simp only [idealGame, ProbComp.eval_bind, ProbComp.eval_uniform, PMF.bind_bind, PMF.bind_map,
    Adversary.ofWord]
  rfl

/-- Exact equality between the word-level and finite correlation-robustness advantages. -/
theorem wordAdvantage_eq_finite (H : CorrelationRobustHash) (adversary : WordAdversary) (n : ℕ) :
    Game.advantage (wordRealGame H adversary n) (wordIdealGame H adversary n) =
      advantage (H.toFinite n)
        (Adversary.ofWord adversary n (H.queries n) (H.keyLength n) (H.outLength n)) := by
  rw [wordRealGame_eq_realGame, wordIdealGame_eq_idealGame, advantage]

/-- Correlation robustness implies computational indistinguishability of the encoded real and
ideal challenge distributions. -/
theorem CorrelationRobustHash.isCorrelationRobust_implies_computationallyIndistinguishable
    {H : CorrelationRobustHash} (hH : H.IsCorrelationRobust) :
    ComputationallyIndistinguishable
      (fun n => (ProbComp.eval (wordRealSample H n)).map encWordTuple)
      (fun n => (ProbComp.eval (wordIdealSample H n)).map encWordTuple) := by
  intro adversary hadv
  let advWord : WordAdversary := fun n pair => adversary n (encWordTuple pair)
  have hprep : ComputableInPolyTime
      (fun p : ℕ × List (List Bool) × List (List Bool) => (p.1, encWordTuple p.2))
      encWordAdvInput (encPair encUnary encBits) := by
    have hfst : ComputableInPolyTime (fun p : ℕ × List (List Bool) × List (List Bool) => p.1)
        encWordAdvInput encUnary := by
      unfold encWordAdvInput
      fun_prop
    have hsnd : ComputableInPolyTime
        (fun p : ℕ × List (List Bool) × List (List Bool) => encWordTuple p.2)
        encWordAdvInput encBits :=
      (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.encode encWordTuple)).comp
        (by unfold encWordAdvInput; fun_prop)
    exact hfst.prod hsnd
  have hadvWord : WordAdversary.IsPPT advWord := IsPPTOn.preprocess hadv hprep
  have hneg := hH advWord hadvWord
  simpa only [wordRealGame, wordIdealGame, distinguishingGame, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, advWord] using hneg

end Cslib.Crypto.CorrelationRobust
