/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Foundations.Data.List.TakeQuantifiers
import CslibFrontier.Tactic.EncLen

/-!
# `Σₖ₊₁` as projections of `Πₖ`

A problem `A` in `Σₖ₊₁` is the projection of a problem `B` in `Πₖ` on pairs of an instance and a
first certificate (`Cslib.Complexity.exists_mem_PiP_of_mem_SigmaP_succ`), the first step of the
collapse of the hierarchy [Arora and Barak, Theorem 5.4][AroraBarak09]. `B` contains the pairs
`(a, w₁)` from which the remaining `k` alternating quantifiers accept, with respect to the encoding
`encPair enc encBits` of pairs. Its blocks of certificates have lengths given by polynomials in the
length of `enc a`, while `Πₖ` asks for polynomials in the length of the encoded pair. The verifier
of `B` therefore reads longer blocks and cuts each to its first bits
(`Cslib.Complexity.truncateBlocks`, an instance of `Cslib.Complexity.takeBlocks`), which does not
change the quantifiers (`Cslib.Complexity.alternation_takeBlocks`).

## Main definitions

* `Cslib.Complexity.takeBlocks`: cut consecutive blocks of a word to their prefixes.
* `Cslib.Complexity.truncateBlocks`: cut blocks of polynomial lengths to shorter blocks.
* `Cslib.Complexity.trimUniformBlocks`: cut uniform-length blocks to polynomial lengths.

## Main results

* `Cslib.Complexity.alternation_takeBlocks`, `Cslib.Complexity.alternation_truncateBlocks`,
  `Cslib.Complexity.alternation_trimUniformBlocks`: cutting longer blocks does not change
  alternating quantifiers.
* `Cslib.Complexity.computableInPolyTime_takeBlocks`,
  `Cslib.Complexity.computableInPolyTime_truncateBlocks`,
  `Cslib.Complexity.computableInPolyTime_trimUniformBlocks`: cutting blocks is polynomial-time.
* `Cslib.Complexity.exists_replicate_of_mem_SigmaP`: every `Σₖ` problem has a verifier with a
  single polynomial bound for all `k` certificate blocks.
* `Cslib.Complexity.exists_mem_PiP_of_mem_SigmaP_succ`: a problem in `Σₖ₊₁` is the projection of
  a problem in `Πₖ` on pairs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-! ### Cutting blocks of certificates -/

/-- The first `l.1` bits of each consecutive block of length `l.2` of `w`, for the pairs `l` of `ls`
in order. -/
def takeBlocks : List (ℕ × ℕ) → List Bool → List Bool
  | [], _ => []
  | l :: ls, w => w.take l.1 ++ takeBlocks ls (w.drop l.2)

/-- **Cutting longer blocks does not change alternating quantifiers**: quantifying over blocks of
lengths `l.2` and cutting each to `l.1 ≤ l.2` bits quantifies over all blocks of lengths `l.1`. -/
theorem alternation_takeBlocks {ls : List (ℕ × ℕ)} (h : ∀ l ∈ ls, l.1 ≤ l.2) {q : Bool}
    {P : List Bool → Prop} :
    Alternation q (ls.map Prod.snd) (fun w => P (takeBlocks ls w)) ↔
      Alternation q (ls.map Prod.fst) P := by
  induction ls generalizing q P with
  | nil => simp [takeBlocks]
  | cons l ls ih =>
    have hl := h l List.mem_cons_self
    -- a long block, appended to anything, cuts to its prefix followed by the cut of the rest
    have key (w : List Bool) (hw : w.length = l.2) {q : Bool} :
        Alternation q (ls.map Prod.snd) (fun v => P (takeBlocks (l :: ls) (w ++ v))) ↔
          Alternation q (ls.map Prod.fst) fun v => P (w.take l.1 ++ v) :=
      (alternation_congr fun v => by
        simp only [takeBlocks, List.take_append_of_le_length (hw ▸ hl), List.drop_left' hw]).trans
        (ih (fun l' hl' => h l' (List.mem_cons_of_mem l hl')) (P := fun v => P (w.take l.1 ++ v)))
    cases q
    · simp only [List.map_cons, alternation_false_cons]
      exact (forall_congr' fun w => imp_congr_right fun hw => key w hw).trans
        (List.forall_length_eq_take_iff (P := fun u => Alternation true (ls.map Prod.fst)
          fun v => P (u ++ v)) hl)
    · simp only [List.map_cons, alternation_true_cons]
      exact (exists_congr fun w => and_congr_right fun hw => key w hw).trans
        (List.exists_length_eq_take_iff (P := fun u => Alternation false (ls.map Prod.fst)
          fun v => P (u ++ v)) hl)

/-- Cutting blocks is polynomial-time, for a fixed list of pairs of block lengths computed in
unary. -/
theorem computableInPolyTime_takeBlocks {γ : Type} {encIn : γ ↪ List Bool}
    (ls : List ((γ → ℕ) × (γ → ℕ)))
    (hL : ∀ l ∈ ls, ComputableInPolyTime l.1 encIn encUnary ∧
      ComputableInPolyTime l.2 encIn encUnary)
    {W : γ → List Bool} (hW : ComputableInPolyTime W encIn encBits) :
    ComputableInPolyTime (fun x => takeBlocks (ls.map fun l => (l.1 x, l.2 x)) (W x))
      encIn encBits := by
  induction ls generalizing W with
  | nil => exact .const []
  | cons l ls ih =>
    have ⟨h₁, h₂⟩ := hL l List.mem_cons_self
    exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsTakeWithInput hW h₁)
      (ih (fun l' hl' => hL l' (List.mem_cons_of_mem l hl'))
        (ComputableInPolyTime.bitsDropWithInput hW h₂))

/-- The blocks of `w` of lengths `p.eval m`, for the polynomials `p` of `ps` in order, each cut to
its first `p.eval n` bits. -/
def truncateBlocks (ps : List (Polynomial ℕ)) (n m : ℕ) : List Bool → List Bool :=
  takeBlocks (ps.map fun p => (p.eval n, p.eval m))

/-- **Cutting longer blocks does not change alternating quantifiers**: quantifying over blocks of
lengths `p.eval m` and cutting each to `p.eval n ≤ p.eval m` bits quantifies over all blocks of
lengths `p.eval n`. -/
theorem alternation_truncateBlocks {ps : List (Polynomial ℕ)} {n m : ℕ} (h : n ≤ m) {q : Bool}
    {P : List Bool → Prop} :
    Alternation q (ps.map fun p => p.eval m) (fun w => P (truncateBlocks ps n m w)) ↔
      Alternation q (ps.map fun p => p.eval n) P := by
  simpa only [truncateBlocks, List.map_map, Function.comp_def] using
    alternation_takeBlocks (ls := ps.map fun p => (p.eval n, p.eval m)) (q := q) (P := P)
      (by simpa only [List.forall_mem_map] using fun p _ => p.eval_mono h)

/-- Cutting blocks is polynomial-time, for a fixed list of polynomials and lengths `n`, `m` computed
in unary. -/
theorem computableInPolyTime_truncateBlocks {γ : Type} {encIn : γ ↪ List Bool}
    (ps : List (Polynomial ℕ)) {N M : γ → ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary) {W : γ → List Bool}
    (hW : ComputableInPolyTime W encIn encBits) :
    ComputableInPolyTime (fun x => truncateBlocks ps (N x) (M x) (W x)) encIn encBits := by
  simpa only [truncateBlocks, List.map_map, Function.comp_def] using
    computableInPolyTime_takeBlocks
      (ps.map fun p => (fun x => p.eval (N x), fun x => p.eval (M x)))
      (fun l hl => by
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hl
        exact ⟨(ComputableInPolyTime.unary_eval p).comp hN,
          (ComputableInPolyTime.unary_eval p).comp hM⟩) hW

/-- Cut consecutive blocks of uniform length `M` to lengths `p.eval n` for `p ∈ ps`. -/
def trimUniformBlocks (ps : List (Polynomial ℕ)) (n M : ℕ) : List Bool → List Bool :=
  takeBlocks (ps.map fun p => (p.eval n, M))

/-- Quantifying over `ps.length` blocks of uniform length `M` and cutting each to `p.eval n ≤ M`
bits quantifies over blocks of lengths `p.eval n`. -/
theorem alternation_trimUniformBlocks {ps : List (Polynomial ℕ)} {n M : ℕ}
    (hle : ∀ p ∈ ps, p.eval n ≤ M) {q : Bool} {P : List Bool → Prop} :
    Alternation q (List.replicate ps.length M) (fun w => P (trimUniformBlocks ps n M w)) ↔
      Alternation q (ps.map fun p => p.eval n) P := by
  simpa only [trimUniformBlocks, List.map_map, Function.comp_def, List.map_const',
    List.length_map] using
    alternation_takeBlocks (ls := ps.map fun p => (p.eval n, M)) (q := q) (P := P)
      (by simpa only [List.forall_mem_map] using hle)

/-- Cutting uniform-length blocks is polynomial-time, for a fixed list of polynomials and lengths
`N`, `M` computed in unary. -/
theorem computableInPolyTime_trimUniformBlocks {γ : Type} {encIn : γ ↪ List Bool}
    (ps : List (Polynomial ℕ)) {N M : γ → ℕ}
    (hN : ComputableInPolyTime N encIn encUnary)
    (hM : ComputableInPolyTime M encIn encUnary) {W : γ → List Bool}
    (hW : ComputableInPolyTime W encIn encBits) :
    ComputableInPolyTime (fun x => trimUniformBlocks ps (N x) (M x) (W x)) encIn encBits := by
  simpa only [trimUniformBlocks, List.map_map, Function.comp_def] using
    computableInPolyTime_takeBlocks
      (ps.map fun p => (fun x => p.eval (N x), M))
      (fun l hl => by
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hl
        exact ⟨(ComputableInPolyTime.unary_eval p).comp hN, hM⟩) hW

/-! ### Uniform block lengths and peeling off the first quantifier -/

variable {α : Type} {enc : α ↪ List Bool}

/-- **Uniform block-length normal form for `Σₖ`:** every `A ∈ SigmaP k enc` can be verified using a
single polynomial `p` for all `k` certificate blocks (`List.replicate k p`), matching
[Arora and Barak, Definition 5.3][AroraBarak09]. -/
theorem exists_replicate_of_mem_SigmaP {k : ℕ} {A : Set α} (hA : A ∈ SigmaP k enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        IsAlternatingVerifier enc true (List.replicate k p) V A := by
  obtain ⟨ps, V, hps, hV, hAV⟩ := hA
  have hlen : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary :=
    (ComputableInPolyTime.encoding_length enc).comp (.fst _ _)
  refine ⟨ps.sum, fun x =>
    V (x.1, trimUniformBlocks ps (enc x.1).length (ps.sum.eval (enc x.1).length) x.2),
    hV.comp ((ComputableInPolyTime.fst _ _).prod
      (computableInPolyTime_trimUniformBlocks ps hlen
        ((ComputableInPolyTime.unary_eval ps.sum).comp hlen) (.snd _ _))),
    fun a => ?_⟩
  rw [hAV a, List.map_replicate, ← hps]
  exact (alternation_trimUniformBlocks fun p hp => by
    rw [Polynomial.eval_listSum]
    exact List.le_sum_of_mem (List.mem_map_of_mem hp)).symm

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
    enc_len
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
