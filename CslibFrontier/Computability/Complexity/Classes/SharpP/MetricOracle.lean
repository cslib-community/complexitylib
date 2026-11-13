/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Counting
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Complexity.Classes.Oracle.QueryBit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
public import CslibFrontier.Languages.Probabilistic.Iteration

/-!
# Metric reductions as oracle computations

Arora and Barak define `FP^f` for `f : {0,1}* → ℕ` as the functions computable in polynomial time
by an oracle machine that may ask for bit `i` of `f x` [Arora and Barak, Section 9.2][AroraBarak07];
here the oracle language answers the bits of `f` (`Cslib.Complexity.AnswersBits`, for instance
`Cslib.Complexity.bitGraph`). A function is #P-complete in their sense (Definition 9.5) when it is
in #P and every function in #P lies in `FP^f`.

A metric reduction `f a = post (a, g (r a))` is such an oracle computation when the values of `g`
have polynomially many bits: the program `Cslib.Complexity.readBitsProgram` asks, one after the
other, for bits `0, 1, …, c a - 1` of `g (r a)`, where `c a` is a polynomial in the length of the
encoded query, reassembles the number, and applies `post`
(`Cslib.Complexity.MetricReducible.polyTimeOracleProgram`). The program is fixed before the
oracle and is correct against every oracle language answering the bits of `g`. Hence
#P-completeness under metric reductions gives #P-completeness in the sense of Arora and Barak
(`Cslib.Complexity.SharpPMetricComplete.computableInPolyTimeWithOracle`).

## Main definitions

* `Cslib.Complexity.readBitsProgram`: ask for the first bits of a counting function's value.

## Main results

* `Cslib.Complexity.MetricReducible.polyTimeOracleProgram`,
  `Cslib.Complexity.MetricReducible.computableInPolyTimeWithOracle`: a metric reduction to a
  function with polynomially many bits is a polynomial-time oracle computation.
* `Cslib.Complexity.SharpPMetricComplete.computableInPolyTimeWithOracle`: every #P function is
  in `FP^f` for a #P-complete `f` under metric reductions (Arora–Barak Definition 9.5).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β Y : Type}

/-- One step of reading bits: ask for the next bit and append it. -/
def readBitStep (req : α → ℕ → List Bool) (a : α) (bits : List Bool) :
    WordQueryComp Unit (List Bool) :=
  (fun b => bits ++ [b]) <$> queryBit (req a bits.length)

/-- Ask for the words `req a 0, …, req a (count a - 1)` in turn and list the answers. -/
def readBitsProgram (req : α → ℕ → List Bool) (count : α → ℕ) (a : α) :
    WordQueryComp Unit (List Bool) :=
  OracleComp.iterate (count a) (readBitStep req a) []

open Classical in
/-- Against an oracle language, `readBitsProgram` lists the memberships of the requested words. -/
theorem interpret_readBitsProgram (A : Set (List Bool)) (req : α → ℕ → List Bool)
    (count : α → ℕ) (a : α) :
    OracleComp.interpret (m := Id) (languageOracle A) (readBitsProgram req count a) =
      List.ofFn fun i : Fin (count a) => decide (req a i ∈ A) := by
  rw [readBitsProgram, OracleComp.interpret_id_iterate]
  have hstep : ∀ s, OracleComp.interpret (m := Id) (languageOracle A) (readBitStep req a s) =
      s ++ [decide (req a s.length ∈ A)] := fun s => by
    rw [readBitStep, OracleComp.interpret_map, interpret_queryBit]
    rfl
  generalize count a = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hstep, List.ofFn_succ_last, List.length_ofFn]
    simp

open ComputableInPolyTime in
theorem isOraclePPTOn_readBitsProgram {encA : α ↪ List Bool} {req : α → ℕ → List Bool}
    {count : α → ℕ}
    (hreq : ComputableInPolyTime (fun p : α × ℕ => req p.1 p.2) (encPair encA encUnary) encBits)
    (hcount : ComputableInPolyTime count encA encUnary) :
    IsOraclePPTOn encA encBits
      (fun a => OracleComp.interpret ProbOracleComp.query (readBitsProgram req count a)) := by
  have hword : ComputableInPolyTime
      (fun pair : α × List Bool => req pair.1 pair.2.length) (encPair encA encBits) encBits :=
    hreq.comp ((fst encA encBits).prod (length_bits.comp (snd encA encBits)))
  have hstep : IsOraclePPTOn (encPair encA encBits) encBits
      (fun pair => OracleComp.interpret ProbOracleComp.query (readBitStep req pair.1 pair.2)) := by
    have h := (isOraclePPTOn_queryBit hword).map_with'
      (f := fun (pair : α × List Bool) (b : Bool) => pair.2 ++ [b]) (by fun_prop)
    refine h.congr fun pair State oracle s => ?_
    simp only [readBitStep, OracleComp.interpret_map]
  have hsize : PolyBounded (fun a => (encA a).length) count := hcount.polyBounded
  have hit := IsOraclePPTOn.iterateWith_spec' (input := encA) (stateEncoding := encBits)
    (count := count) (initial := fun _ => []) (step := fun a s =>
      OracleComp.interpret ProbOracleComp.query (readBitStep req a s))
    hcount (by fun_prop) hstep (fun _ i s => s.length = i) (fun _ => rfl)
    (fun a i s _ hs next hnext => by
      simp only [readBitStep, OracleComp.interpret_map] at hnext
      obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      simp [hs])
    hsize (fun a i s hi hs => by simpa [hs] using hi)
  simpa only [readBitsProgram, OracleComp.interpret_iterate] using hit.1

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encY : Y ↪ List Bool}

/-- **A metric reduction is a polynomial-time oracle program.** If `f` reduces by a metric
reduction to `g`, whose values have fewer than `p (|encB b|)` bits for a polynomial `p`, then one
polynomial-time oracle program computes `f` against every oracle language answering the bits of
`g`: it reads the bits of `g (r a)` and applies the recovery map. -/
theorem MetricReducible.polyTimeOracleProgram {f : α → Y} {g : β → ℕ}
    (h : MetricReducible encA encB encY encNat f g) {p : Polynomial ℕ}
    (hp : ∀ b, g b < 2 ^ p.eval (encB b).length) :
    PolyTimeOracleProgram encA encY (AnswersBits encB g) (· = f) := by
  classical
  obtain ⟨r, post, hr, hpost, hfg⟩ := h
  let req : α → ℕ → List Bool := fun a i => encPair encB encNat (r a, i)
  let count : α → ℕ := fun a => p.eval (encB (r a)).length
  have hreq : ComputableInPolyTime (fun q : α × ℕ => req q.1 q.2) (encPair encA encUnary)
      encBits :=
    ComputableInPolyTime.encoding_comp (f := fun q : α × ℕ => (r q.1, q.2))
      ((hr.comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)))
  have hcount : ComputableInPolyTime count encA encUnary := by
    have : ComputableInPolyTime (fun b => p.eval (encB b).length) encB encUnary := by fun_prop
    exact this.comp hr
  have hread := isOraclePPTOn_readBitsProgram hreq hcount
  have hpost' : ComputableInPolyTime (fun q : α × List Bool => post (q.1, ofBits q.2))
      (encPair encA encBits) encY :=
    hpost.comp ((ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.bitsToNat.comp (ComputableInPolyTime.snd _ _)))
  refine ⟨fun a => (fun bits => post (a, ofBits bits)) <$> readBitsProgram req count a,
    ?_, fun A hA => funext fun a => ?_⟩
  · simpa only [OracleComp.interpret_map] using hread.map_with' hpost'
  · rw [OracleComp.interpret_map, interpret_readBitsProgram, hfg a]
    have hbits : (List.ofFn fun i : Fin (count a) => decide (req a i ∈ A)) =
        Cslib.BitString.lowBits (count a) (g (r a)) := by
      refine List.ext_getElem (by simp [Cslib.BitString.lowBits]) fun i h₁ h₂ => ?_
      simp only [List.getElem_ofFn, Cslib.BitString.lowBits, List.getElem_map,
        List.getElem_range, req]
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact hA (r a) i
    change post (a, ofBits (List.ofFn _)) = _
    rw [hbits, ofBits_lowBits (hp (r a))]

/-- A metric reduction to a function `g` with polynomially many bits makes `f` computable in
polynomial time relative to the bit graph of `g`: `f ∈ FP^g` in the sense of Arora and Barak. -/
theorem MetricReducible.computableInPolyTimeWithOracle {f : α → Y} {g : β → ℕ}
    (h : MetricReducible encA encB encY encNat f g) {p : Polynomial ℕ}
    (hp : ∀ b, g b < 2 ^ p.eval (encB b).length) :
    ComputableInPolyTimeWithOracle (bitGraph encB g) f encA encY := by
  obtain ⟨_, hg, rfl⟩ := (h.polyTimeOracleProgram hp).exists_computableInPolyTimeWithOracle
    (answersBits_bitGraph encB g)
  exact hg

/-- **#P-completeness under metric reductions gives #P-completeness in the sense of Arora and
Barak** (Definition 9.5): every function in #P is computable in polynomial time relative to the
bit graph of a #P-complete function. -/
theorem SharpPMetricComplete.computableInPolyTimeWithOracle {g : β → ℕ}
    (hg : SharpPMetricComplete encB g) {f : α → ℕ} (hf : f ∈ SharpP encA) :
    ComputableInPolyTimeWithOracle (bitGraph encB g) f encA encNat := by
  obtain ⟨p, hp⟩ := SharpP.exists_le_two_pow hg.1
  refine (hg.2 _ _ hf).computableInPolyTimeWithOracle (p := p + 1) fun b => ?_
  calc g b ≤ 2 ^ p.eval (encB b).length := hp b
    _ < 2 ^ (p + 1).eval (encB b).length := Nat.pow_lt_pow_right (by norm_num) (by simp)

end Cslib.Complexity
