/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# `Σₖ₊₁` as projections of `Πₖ`

A problem `A` in `Σₖ₊₁` is the projection of a problem `B` in `Πₖ` on pairs of an instance and a
first certificate (`Cslib.Complexity.exists_mem_PiP_of_mem_SigmaP_succ`), the first step of the
collapse of the hierarchy [Arora and Barak, Theorem 5.4][AroraBarak09]. `B` contains the pairs
`(a, w₁)` from which the remaining `k` alternating quantifiers accept, with respect to the encoding
`encPair enc encBits` of pairs. Its blocks of certificates have lengths given by polynomials in the
length of `enc a`, while `Πₖ` asks for polynomials in the length of the encoded pair. The verifier
of `B` therefore reads longer blocks and cuts each to its first bits
(`Cslib.Complexity.truncateBlocks`), which does not change the quantifiers
(`Cslib.Complexity.alternation_truncateBlocks`).

## Main definitions

* `Cslib.Complexity.truncateBlocks`: cut blocks of certificates to shorter blocks.

## Main results

* `Cslib.Complexity.alternation_truncateBlocks`: cutting longer blocks does not change
  alternating quantifiers.
* `Cslib.Complexity.computableInPolyTime_truncateBlocks`: cutting blocks is polynomial-time.
* `Cslib.Complexity.exists_mem_PiP_of_mem_SigmaP_succ`: a problem in `Σₖ₊₁` is the projection of
  a problem in `Πₖ` on pairs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-! ### Cutting blocks of certificates -/

/-- The blocks of `w` of lengths `p.eval m`, for the polynomials `p` of `ps` in order, each cut to
its first `p.eval n` bits. -/
def truncateBlocks : List (Polynomial ℕ) → ℕ → ℕ → List Bool → List Bool
  | [], _, _, _ => []
  | p :: ps, n, m, w => w.take (p.eval n) ++ truncateBlocks ps n m (w.drop (p.eval m))

/-- **Cutting longer blocks does not change alternating quantifiers**: quantifying over blocks of
lengths `p.eval m` and cutting each to `p.eval n ≤ p.eval m` bits quantifies over all blocks of
lengths `p.eval n`. -/
theorem alternation_truncateBlocks {ps : List (Polynomial ℕ)} {n m : ℕ} (h : n ≤ m) {q : Bool}
    {P : List Bool → Prop} :
    Alternation q (ps.map fun p => p.eval m) (fun w => P (truncateBlocks ps n m w)) ↔
      Alternation q (ps.map fun p => p.eval n) P := by
  induction ps generalizing q P with
  | nil => simp [truncateBlocks]
  | cons p ps ih =>
    have hle := p.eval_mono h
    -- a long block, appended to anything, cuts to its first `p.eval n` bits
    have hcut (w v : List Bool) (hw : w.length = p.eval m) :
        truncateBlocks (p :: ps) n m (w ++ v) = w.take (p.eval n) ++ truncateBlocks ps n m v := by
      simp only [truncateBlocks, List.take_append_of_le_length (hw ▸ hle),
        List.drop_left' hw]
    have key (w : List Bool) (hw : w.length = p.eval m) {q : Bool} :
        Alternation q (ps.map fun p => p.eval m)
          (fun v => P (truncateBlocks (p :: ps) n m (w ++ v))) ↔
        Alternation q (ps.map fun p => p.eval n) fun v => P (w.take (p.eval n) ++ v) :=
      (alternation_congr fun v => by rw [hcut w v hw]).trans
        (ih (P := fun v => P (w.take (p.eval n) ++ v)))
    -- a short block is the cut of its padding
    have hpad (w : List Bool) (hw : w.length = p.eval n) :
        (w ++ List.replicate (p.eval m - p.eval n) false).length = p.eval m := by
      simp only [List.length_append, List.length_replicate, hw]
      omega
    have htake (w : List Bool) (hw : w.length = p.eval n) :
        (w ++ List.replicate (p.eval m - p.eval n) false).take (p.eval n) = w := by
      rw [← hw, List.take_left]
    have hlen (w : List Bool) (hw : w.length = p.eval m) : (w.take (p.eval n)).length = p.eval n :=
      by rw [List.length_take, hw, Nat.min_eq_left hle]
    cases q
    · simp only [List.map_cons, alternation_false_cons]
      constructor
      · intro hP w hw
        have := (key _ (hpad w hw)).mp (hP _ (hpad w hw))
        rwa [htake w hw] at this
      · intro hP w hw
        exact (key w hw).mpr (hP _ (hlen w hw))
    · simp only [List.map_cons, alternation_true_cons]
      constructor
      · rintro ⟨w, hw, hP⟩
        exact ⟨_, hlen w hw, (key w hw).mp hP⟩
      · rintro ⟨w, hw, hP⟩
        refine ⟨_, hpad w hw, (key _ (hpad w hw)).mpr ?_⟩
        rwa [htake w hw]

/-- Cutting blocks is polynomial-time, for a fixed list of polynomials and lengths `n`, `m` computed
in unary. -/
theorem computableInPolyTime_truncateBlocks {γ : Type} {encIn : γ ↪ List Bool}
    (ps : List (Polynomial ℕ)) {N M : γ → ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary) {W : γ → List Bool}
    (hW : ComputableInPolyTime W encIn encBits) :
    ComputableInPolyTime (fun x => truncateBlocks ps (N x) (M x) (W x)) encIn encBits := by
  induction ps generalizing W with
  | nil => exact .const []
  | cons p ps ih =>
    exact ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsTakeWithInput hW
        ((ComputableInPolyTime.unary_eval p).comp hN))
      (ih (ComputableInPolyTime.bitsDropWithInput hW
        ((ComputableInPolyTime.unary_eval p).comp hM)))

/-! ### Peeling off the first quantifier -/

variable {α : Type} {enc : α ↪ List Bool}

/-- **A problem in `Σₖ₊₁` is the projection of a problem in `Πₖ`**, as in the proof of
[Arora and Barak, Theorem 5.4][AroraBarak09]: there are a polynomial `p` and a problem `B` in `Πₖ`
on pairs of an instance and a word, encoded by `encPair enc encBits`, such that `a ∈ A` iff some
word `w` of length `p (enc a).length` has `(a, w) ∈ B`. -/
theorem exists_mem_PiP_of_mem_SigmaP_succ {k : ℕ} {A : Set α} (hA : A ∈ SigmaP (k + 1) enc) :
    ∃ (p : Polynomial ℕ) (B : Set (α × List Bool)), B ∈ PiP k (encPair enc encBits) ∧
      ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ B := by
  obtain ⟨ps, V, hlen, hV, hA⟩ := hA
  obtain ⟨p, ps, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  have hlen' : ps.length = k := by simpa using hlen
  -- the pairs `(a, w₁)` from which the last `k` quantifiers accept
  let B : Set (α × List Bool) := {y | Alternation false
    (ps.map fun r => r.eval (enc y.1).length) fun w => V (y.1, y.2 ++ w) = true}
  have hle (y : α × List Bool) : (enc y.1).length ≤ (encPair enc encBits y).length := by
    simp only [length_encPair]
    omega
  refine ⟨p, B, ⟨ps, fun z => V (z.1.1, z.1.2 ++ truncateBlocks ps (enc z.1.1).length
      (encPair enc encBits z.1).length z.2), hlen', ?_, fun y => ?_⟩, hA⟩
  · have hfst := (ComputableInPolyTime.fst (encPair enc encBits) encBits)
    exact hV.comp (((ComputableInPolyTime.fst _ _).comp hfst).prod
      (ComputableInPolyTime.bitsAppend ((ComputableInPolyTime.snd _ _).comp hfst)
        (computableInPolyTime_truncateBlocks ps
          (((ComputableInPolyTime.encoding_length enc).comp
            ((ComputableInPolyTime.fst _ _).comp hfst)))
          (((ComputableInPolyTime.encoding_length _).comp hfst))
            (.snd _ _))))
  · exact (alternation_truncateBlocks (hle y) (P := fun w => V (y.1, y.2 ++ w) = true)).symm

end Cslib.Complexity
