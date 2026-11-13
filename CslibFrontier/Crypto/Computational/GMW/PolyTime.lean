/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.OracleSimulation
public import CslibFrontier.Crypto.Computational.GMW.Protocol
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Crypto.Game.Retry
public import CslibFrontier.Logics.Propositional.CNF.Encoding
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Polynomial-time and PPT certificates for the 3-copy GMW protocol

This module registers `@[fun_prop]` polynomial-time and strict-(oracle-)PPT certificates for the
3-copy masked-3SAT GMW protocol gadgets defined in
`CslibFrontier.Crypto.Computational.GMW.Protocol`,
proves that `runTwoRound` preserves strict PPT when driven by polynomial-time round functions and a
strict oracle PPT verifier (`isPPTOn_runTwoRound`), defines the zero-knowledge simulator
`gmwSimulator` (via `gmwSampleSimCoins`, `gmwSimWithPads`, `gmwSimAttempt` and `firstSuccess`), and
certifies:

* `isOraclePPTOn_gmwVerifier`: the honest verifier `gmwVerifier` is uniform strict oracle PPT;
* `isPPTOn_gmwInteract`: running any uniform strict oracle PPT verifier against the honest prover is
  uniform strict PPT;
* `isPPTOn_gmwSimulator`: the GMW zero-knowledge simulator `gmwSimulator` is uniform strict PPT.

## Main definitions

* `Cslib.Crypto.GMW.encTwoRoundState`, `Cslib.Crypto.GMW.encProverCoins`: the encodings of the
  state of `runTwoRound` and of the prover's coins.
* `Cslib.Crypto.GMW.gmwSampleSimCoins`, `Cslib.Crypto.GMW.gmwSimWithPads`,
  `Cslib.Crypto.GMW.gmwSimAttempt`: single-attempt GMW simulator components. An attempt returns
  `some` view when its guess hits the verifier's challenge and `none` otherwise (`acceptGuess`).
* `Cslib.Crypto.GMW.gmwSimulator`: the GMW zero-knowledge simulator repeating `gmwSimAttempt`
  `n + 1` times.

## Main results

* `Cslib.Crypto.GMW.isOraclePPTOn_gmwVerifier`: `gmwVerifier` is `IsOraclePPTOn`.
* `Cslib.Crypto.GMW.isPPTOn_gmwInteract`: `gmwInteract` is `IsPPTOn`.
* `Cslib.Crypto.GMW.isPPTOn_gmwSimulator`: `gmwSimulator` is `IsPPTOn`.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
-/

@[expose] public section

namespace Cslib.Crypto.GMW

open Probability Complexity Logic.PL Turing.MultiTapeTM

/-! ### Polynomial-time certificates for protocol gadgets -/

private theorem bool_xor' {α : Type} {input : α ↪ List Bool} {f g : α → Bool}
    (hf : ComputableInPolyTime f input encBool) (hg : ComputableInPolyTime g input encBool) :
    ComputableInPolyTime (fun a => f a ^^ g a) input encBool :=
  ComputableInPolyTime.bool_xor.comp (hf.prod hg)

private theorem computableInPolyTime_clauseLitVar (i : ℕ) {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ} (hc : ComputableInPolyTime c input (encClause encNat)) :
    ComputableInPolyTime (fun a => ((c a).getD i (0, false)).1) input encNat :=
  (hc.listGetDWithInput (.const i) (0, false)).fst'

private theorem computableInPolyTime_clauseLitPol (i : ℕ) {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ} (hc : ComputableInPolyTime c input (encClause encNat)) :
    ComputableInPolyTime (fun a => ((c a).getD i (0, false)).2) input encBool :=
  (hc.listGetDWithInput (.const i) (0, false)).snd'

@[fun_prop]
theorem computableInPolyTime_gmwBit0Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => gmwBit0Of8 (t a)) input encBool :=
  ComputableInPolyTime.bool_or.comp
    ((ComputableInPolyTime.bool_or.comp
      ((ComputableInPolyTime.bool_or.comp
        ((ht.beq (.const 1)).prod (ht.beq (.const 3)))).prod
        (ht.beq (.const 5)))).prod
      (ht.beq (.const 7)))

@[fun_prop]
theorem computableInPolyTime_gmwBit1Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => gmwBit1Of8 (t a)) input encBool :=
  ComputableInPolyTime.bool_or.comp
    ((ComputableInPolyTime.bool_or.comp
      ((ComputableInPolyTime.bool_or.comp
        ((ht.beq (.const 2)).prod (ht.beq (.const 3)))).prod
        (ht.beq (.const 6)))).prod
      (ht.beq (.const 7)))

@[fun_prop]
theorem computableInPolyTime_gmwBit2Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => gmwBit2Of8 (t a)) input encBool :=
  ComputableInPolyTime.bool_or.comp
    ((ComputableInPolyTime.bool_or.comp
      ((ComputableInPolyTime.bool_or.comp
        ((ht.beq (.const 4)).prod (ht.beq (.const 5)))).prod
        (ht.beq (.const 6)))).prod
      (ht.beq (.const 7)))

@[fun_prop]
theorem computableInPolyTime_gmwActiveIdx {α : Type} {input : α ↪ List Bool}
    {b₀ b₁ b₂ : α → Bool} (hb₀ : ComputableInPolyTime b₀ input encBool)
    (hb₁ : ComputableInPolyTime b₁ input encBool) (hb₂ : ComputableInPolyTime b₂ input encBool) :
    ComputableInPolyTime (fun a => gmwActiveIdx (b₀ a) (b₁ a) (b₂ a)) input encUnary :=
  ((hb₀.ite' (.const 1) (.const 0)).unary_add'
    ((ComputableInPolyTime.const 2).unary_mul' (hb₁.ite' (.const 1) (.const 0)))).unary_add'
    ((ComputableInPolyTime.const 4).unary_mul' (hb₂.ite' (.const 1) (.const 0)))

@[fun_prop]
theorem computableInPolyTime_clauseEvalBits {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ} {b₀ b₁ b₂ : α → Bool}
    (hc : ComputableInPolyTime c input (encClause encNat))
    (hb₀ : ComputableInPolyTime b₀ input encBool) (hb₁ : ComputableInPolyTime b₁ input encBool)
    (hb₂ : ComputableInPolyTime b₂ input encBool) :
    ComputableInPolyTime (fun a => clauseEvalBits (c a) (b₀ a) (b₁ a) (b₂ a)) input encBool :=
  let hlen := SAT.computableInPolyTime_clause_length hc
  ComputableInPolyTime.bool_or.comp
    ((ComputableInPolyTime.bool_or.comp
      ((((ComputableInPolyTime.const 0).unary_lt' hlen).bool_and'
        (hb₀.beq (computableInPolyTime_clauseLitPol 0 hc))).prod
      (((ComputableInPolyTime.const 1).unary_lt' hlen).bool_and'
        (hb₁.beq (computableInPolyTime_clauseLitPol 1 hc))))).prod
      (((ComputableInPolyTime.const 2).unary_lt' hlen).bool_and'
        (hb₂.beq (computableInPolyTime_clauseLitPol 2 hc))))

@[fun_prop]
theorem computableInPolyTime_varBit {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {vec : α → List Bool} {v : α → ℕ}
    (hφ : ComputableInPolyTime φ input encCNF) (hvec : ComputableInPolyTime vec input encBits)
    (hv : ComputableInPolyTime v input encNat) :
    ComputableInPolyTime (fun a => varBit (φ a) (vec a) (v a)) input encBool := by
  have hidx := (SAT.computableInPolyTime_vars.comp hφ).idxOfWithInput hv
  simpa only [varBit, Function.comp_apply, decide_eq_true_eq] using
    (hidx.unary_lt' (SAT.computableInPolyTime_vars_length hφ)).ite'
      (hvec.bitsGetDWithInput hidx false) (.const false)

@[fun_prop]
theorem computableInPolyTime_clauseTableRow {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {m : α → List Bool} {c : α → Clause ℕ}
    (hφ : ComputableInPolyTime φ input encCNF) (hm : ComputableInPolyTime m input encBits)
    (hc : ComputableInPolyTime c input (encClause encNat)) :
    ComputableInPolyTime (fun a => clauseTableRow (φ a) (m a) (c a)) input encBits := by
  have hfst := ComputableInPolyTime.fst input encUnary
  have hsnd := ComputableInPolyTime.snd input encUnary
  have hφ1 := hφ.comp hfst; have hm1 := hm.comp hfst; have hc1 := hc.comp hfst
  dsimp only [clauseTableRow]
  apply (ComputableInPolyTime.const (List.range 8)).mapToBitsWithInput (enc := encUnary)
  exact computableInPolyTime_clauseEvalBits hc1
    (bool_xor' (computableInPolyTime_gmwBit0Of8 hsnd)
      (computableInPolyTime_varBit hφ1 hm1 (computableInPolyTime_clauseLitVar 0 hc1)))
    (bool_xor' (computableInPolyTime_gmwBit1Of8 hsnd)
      (computableInPolyTime_varBit hφ1 hm1 (computableInPolyTime_clauseLitVar 1 hc1)))
    (bool_xor' (computableInPolyTime_gmwBit2Of8 hsnd)
      (computableInPolyTime_varBit hφ1 hm1 (computableInPolyTime_clauseLitVar 2 hc1)))

@[fun_prop]
theorem computableInPolyTime_clauseActiveRow {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {v : α → List Bool} {c : α → Clause ℕ}
    (hφ : ComputableInPolyTime φ input encCNF) (hv : ComputableInPolyTime v input encBits)
    (hc : ComputableInPolyTime c input (encClause encNat)) :
    ComputableInPolyTime (fun a => clauseActiveRow (φ a) (v a) (c a)) input encBits := by
  have hfst := ComputableInPolyTime.fst input encUnary
  have hsnd := ComputableInPolyTime.snd input encUnary
  have hφ1 := hφ.comp hfst; have hv1 := hv.comp hfst; have hc1 := hc.comp hfst
  dsimp only [clauseActiveRow]
  apply (ComputableInPolyTime.const (List.range 8)).mapToBitsWithInput (enc := encUnary)
  exact hsnd.decide_eq'
    (computableInPolyTime_gmwActiveIdx
      (computableInPolyTime_varBit hφ1 hv1 (computableInPolyTime_clauseLitVar 0 hc1))
      (computableInPolyTime_varBit hφ1 hv1 (computableInPolyTime_clauseLitVar 1 hc1))
      (computableInPolyTime_varBit hφ1 hv1 (computableInPolyTime_clauseLitVar 2 hc1)))

@[fun_prop]
theorem computableInPolyTime_tableBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {m : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hm : ComputableInPolyTime m input encBits) :
    ComputableInPolyTime (fun a => tableBits (φ a) (m a)) input encBits :=
  (hφ.mapWithInput (computableInPolyTime_clauseTableRow
    (hφ.comp (.fst input _)) (hm.comp (.fst input _)) (.snd input _))).bitsFlatten

@[fun_prop]
theorem computableInPolyTime_activeTableFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {v : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hv : ComputableInPolyTime v input encBits) :
    ComputableInPolyTime (fun a => activeTableFlags (φ a) (v a)) input encBits :=
  (hφ.mapWithInput (computableInPolyTime_clauseActiveRow
    (hφ.comp (.fst input _)) (hv.comp (.fst input _)) (.snd input _))).bitsFlatten

@[fun_prop]
theorem computableInPolyTime_copyLen {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ input encCNF) :
    ComputableInPolyTime (fun a => copyLen (φ a)) input encUnary :=
  ((ComputableInPolyTime.const 2).unary_mul' (SAT.computableInPolyTime_vars_length hφ)).unary_add'
    ((ComputableInPolyTime.const 8).unary_mul' (SAT.computableInPolyTime_length hφ))

@[fun_prop]
theorem computableInPolyTime_totalLen {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ input encCNF) :
    ComputableInPolyTime (fun a => totalLen (φ a)) input encUnary :=
  (ComputableInPolyTime.const 3).unary_mul' (computableInPolyTime_copyLen hφ)

@[fun_prop]
theorem computableInPolyTime_mPart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => mPart (φ a) (copy a)) input encBits :=
  hcopy.bitsTakeWithInput (SAT.computableInPolyTime_vars_length hφ)

@[fun_prop]
theorem computableInPolyTime_vPart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => vPart (φ a) (copy a)) input encBits :=
  let hvars := SAT.computableInPolyTime_vars_length hφ
  (hcopy.bitsDropWithInput hvars).bitsTakeWithInput hvars

@[fun_prop]
theorem computableInPolyTime_tablePart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => tablePart (φ a) (copy a)) input encBits :=
  (hcopy.bitsDropWithInput ((ComputableInPolyTime.const 2).unary_mul'
    (SAT.computableInPolyTime_vars_length hφ))).bitsTakeWithInput
    ((ComputableInPolyTime.const 8).unary_mul' (SAT.computableInPolyTime_length hφ))

@[fun_prop]
theorem computableInPolyTime_realCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {w m : α → List Bool} (hφ : ComputableInPolyTime φ input encCNF)
    (hw : ComputableInPolyTime w input encBits) (hm : ComputableInPolyTime m input encBits) :
    ComputableInPolyTime (fun a => realCopyBits (φ a) (w a) (m a)) input encBits :=
  let hvars := SAT.computableInPolyTime_vars_length hφ
  ((hvars.bitsRowWithInput (.const 0) hm).bitsAppend
    (hvars.bitsXorWithInput (hw.cons' (hm.cons' (.const []))))).bitsAppend
    (computableInPolyTime_tableBits hφ hm)

@[fun_prop]
theorem computableInPolyTime_simCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {rand : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hb : ComputableInPolyTime b input encBool)
    (hrand : ComputableInPolyTime rand input encBits) :
    ComputableInPolyTime (fun a => simCopyBits (φ a) (b a) (rand a)) input encBits :=
  let hvars := SAT.computableInPolyTime_vars_length hφ
  let hrep := (ComputableInPolyTime.bitsReplicate false).comp hvars
  let hrow := hvars.bitsRowWithInput (.const 0) hrand
  hb.ite' ((hrep.bitsAppend hrow).bitsAppend (computableInPolyTime_activeTableFlags hφ hrand))
    ((hrow.bitsAppend hrep).bitsAppend (computableInPolyTime_tableBits hφ hrand))

@[fun_prop]
theorem computableInPolyTime_copyOpenFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hb : ComputableInPolyTime b input encBool)
    (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => copyOpenFlags (φ a) (b a) (copy a)) input encBits :=
  let hvars := SAT.computableInPolyTime_vars_length hφ
  let hfalse := (ComputableInPolyTime.bitsReplicate false).comp hvars
  let htrue := (ComputableInPolyTime.bitsReplicate true).comp hvars
  hb.ite' ((hfalse.bitsAppend htrue).bitsAppend
      (computableInPolyTime_activeTableFlags hφ (computableInPolyTime_vPart hφ hcopy)))
    ((htrue.bitsAppend hfalse).bitsAppend
      ((ComputableInPolyTime.bitsReplicate true).comp
        ((ComputableInPolyTime.const 8).unary_mul' (SAT.computableInPolyTime_length hφ))))

@[fun_prop]
theorem computableInPolyTime_verifyCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hb : ComputableInPolyTime b input encBool)
    (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => verifyCopyBits (φ a) (b a) (copy a)) input encBool :=
  let hfst := ComputableInPolyTime.fst input encUnary
  let hsnd := ComputableInPolyTime.snd input encUnary
  let hφ1 := hφ.comp hfst; let hcopy1 := hcopy.comp hfst
  hb.ite'
    ((ComputableInPolyTime.unary_range'
      ((ComputableInPolyTime.const 8).unary_mul' (SAT.computableInPolyTime_length hφ))).allWithInput
      (ComputableInPolyTime.bool_or.comp
        ((ComputableInPolyTime.bool_not.comp
          ((computableInPolyTime_activeTableFlags hφ1
            (computableInPolyTime_vPart hφ1 hcopy1)).bitsGetDWithInput hsnd false)).prod
        ((computableInPolyTime_tablePart hφ1 hcopy1).bitsGetDWithInput hsnd false))))
    ((computableInPolyTime_tablePart hφ hcopy).beq
      (computableInPolyTime_tableBits hφ (computableInPolyTime_mPart hφ hcopy)))

@[fun_prop]
theorem computableInPolyTime_gmwCopy0 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => gmwCopy0 (φ a) (bits a)) input encBits :=
  hbits.bitsTakeWithInput (computableInPolyTime_copyLen hφ)

@[fun_prop]
theorem computableInPolyTime_gmwCopy1 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => gmwCopy1 (φ a) (bits a)) input encBits :=
  let hlen := computableInPolyTime_copyLen hφ
  (hbits.bitsDropWithInput hlen).bitsTakeWithInput hlen

@[fun_prop]
theorem computableInPolyTime_gmwCopy2 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => gmwCopy2 (φ a) (bits a)) input encBits :=
  let hlen := computableInPolyTime_copyLen hφ
  (hbits.bitsDropWithInput ((ComputableInPolyTime.const 2).unary_mul' hlen)).bitsTakeWithInput hlen

@[fun_prop]
theorem computableInPolyTime_realBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {w m₀ m₁ m₂ : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hw : ComputableInPolyTime w input encBits)
    (hm₀ : ComputableInPolyTime m₀ input encBits) (hm₁ : ComputableInPolyTime m₁ input encBits)
    (hm₂ : ComputableInPolyTime m₂ input encBits) :
    ComputableInPolyTime (fun a => realBits (φ a) (w a) (m₀ a) (m₁ a) (m₂ a)) input encBits :=
  ((computableInPolyTime_realCopyBits hφ hw hm₀).bitsAppend
    (computableInPolyTime_realCopyBits hφ hw hm₁)).bitsAppend
    (computableInPolyTime_realCopyBits hφ hw hm₂)

@[fun_prop]
theorem computableInPolyTime_simBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {ch r₀ r₁ r₂ : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hch : ComputableInPolyTime ch input encBits)
    (hr₀ : ComputableInPolyTime r₀ input encBits) (hr₁ : ComputableInPolyTime r₁ input encBits)
    (hr₂ : ComputableInPolyTime r₂ input encBits) :
    ComputableInPolyTime (fun a => simBits (φ a) (ch a) (r₀ a) (r₁ a) (r₂ a)) input encBits :=
  ((computableInPolyTime_simCopyBits hφ (hch.bitsGetDWithInput (.const 0) false) hr₀).bitsAppend
    (computableInPolyTime_simCopyBits hφ (hch.bitsGetDWithInput (.const 1) false) hr₁)).bitsAppend
    (computableInPolyTime_simCopyBits hφ (hch.bitsGetDWithInput (.const 2) false) hr₂)

@[fun_prop]
theorem computableInPolyTime_allOpenFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {ch bits : α → List Bool} (hφ : ComputableInPolyTime φ input encCNF)
    (hch : ComputableInPolyTime ch input encBits)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => allOpenFlags (φ a) (ch a) (bits a)) input encBits :=
  ((computableInPolyTime_copyOpenFlags hφ (hch.bitsGetDWithInput (.const 0) false)
      (computableInPolyTime_gmwCopy0 hφ hbits)).bitsAppend
    (computableInPolyTime_copyOpenFlags hφ (hch.bitsGetDWithInput (.const 1) false)
      (computableInPolyTime_gmwCopy1 hφ hbits))).bitsAppend
    (computableInPolyTime_copyOpenFlags hφ (hch.bitsGetDWithInput (.const 2) false)
      (computableInPolyTime_gmwCopy2 hφ hbits))

@[fun_prop]
theorem computableInPolyTime_proverReply1 {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {m : α → ℕ}
    {r openFlags bits : α → List Bool} {seeds pads : α → List (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hm : ComputableInPolyTime m input encUnary) (hr : ComputableInPolyTime r input encBits)
    (hopen : ComputableInPolyTime openFlags input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (hseeds : ComputableInPolyTime seeds input (encList encBits))
    (hpads : ComputableInPolyTime pads input (encList encBits)) :
    ComputableInPolyTime
      (fun a => proverReply1 generator (m a) (r a) (openFlags a) (bits a) (seeds a) (pads a))
      input encBits :=
  (computableInPolyTime_naorCommitSplit hg (hm.bitsRowWithInput (.const 0) hr)
    hopen hbits hseeds hpads).bitsFlatten.bitsTakeWithInput
    (hbits.length_bits_comp.unary_mul' hm)

@[fun_prop]
theorem computableInPolyTime_proverReply2 {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {ch bits : α → List Bool} {seeds : α → List (List Bool)}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hch : ComputableInPolyTime ch input encBits) (hbits : ComputableInPolyTime bits input encBits)
    (hseeds : ComputableInPolyTime seeds input (encList encBits)) :
    ComputableInPolyTime (fun a => proverReply2 (s a) (φ a) (ch a) (bits a) (seeds a))
      input encBits :=
  let hflags := computableInPolyTime_allOpenFlags hφ hch hbits
  (computableInPolyTime_naorMaskBits hflags hbits).bitsAppend
    (computableInPolyTime_naorSelectSeeds hs hflags hbits hseeds).bitsFlatten

@[fun_prop]
theorem computableInPolyTime_verifyCommitments {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {r flags commitReply openedBits openSeedsFlat : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hs : ComputableInPolyTime s input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hφ : ComputableInPolyTime φ input encCNF) (hr : ComputableInPolyTime r input encBits)
    (hflags : ComputableInPolyTime flags input encBits)
    (hcommit : ComputableInPolyTime commitReply input encBits)
    (hopened : ComputableInPolyTime openedBits input encBits)
    (hseeds : ComputableInPolyTime openSeedsFlat input encBits) :
    ComputableInPolyTime
      (fun a => verifyCommitments generator (s a) (m a) (φ a) (r a) (flags a)
        (commitReply a) (openedBits a) (openSeedsFlat a))
      input encBool :=
  let hfst := ComputableInPolyTime.fst input encUnary
  let hsnd := ComputableInPolyTime.snd input encUnary
  let hm1 := hm.comp hfst
  (ComputableInPolyTime.unary_range' (computableInPolyTime_totalLen hφ)).allWithInput
    (ComputableInPolyTime.bool_or.comp
      ((ComputableInPolyTime.bool_not.comp ((hflags.comp hfst).bitsGetDWithInput hsnd false)).prod
      ((computableInPolyTime_naorCommit hg (hm1.bitsRowWithInput (.const 0) (hr.comp hfst))
          ((hopened.comp hfst).bitsGetDWithInput hsnd false)
          ((hs.comp hfst).bitsRowWithInput hsnd (hseeds.comp hfst))).beq
        (hm1.bitsRowWithInput hsnd (hcommit.comp hfst)))))

@[fun_prop]
theorem computableInPolyTime_verifyTranscript {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {r commitReply ch openReply : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hs : ComputableInPolyTime s input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hφ : ComputableInPolyTime φ input encCNF) (hr : ComputableInPolyTime r input encBits)
    (hcommit : ComputableInPolyTime commitReply input encBits)
    (hch : ComputableInPolyTime ch input encBits)
    (hopen : ComputableInPolyTime openReply input encBits) :
    ComputableInPolyTime
      (fun a => verifyTranscript generator (s a) (m a) (φ a) (r a)
        (commitReply a) (ch a) (openReply a))
      input encBool :=
  let hK := computableInPolyTime_totalLen hφ
  let hopened := hopen.bitsTakeWithInput hK; let hseeds := hopen.bitsDropWithInput hK
  let hflags := computableInPolyTime_allOpenFlags hφ hch hopened
  ((((hφ.allWithInput
    ((SAT.computableInPolyTime_clause_length (.snd input _)).unary_le' (.const 3))).bool_and'
    (computableInPolyTime_verifyCopyBits hφ (hch.bitsGetDWithInput (.const 0) false)
      (computableInPolyTime_gmwCopy0 hφ hopened))).bool_and'
    (computableInPolyTime_verifyCopyBits hφ (hch.bitsGetDWithInput (.const 1) false)
      (computableInPolyTime_gmwCopy1 hφ hopened))).bool_and'
    (computableInPolyTime_verifyCopyBits hφ (hch.bitsGetDWithInput (.const 2) false)
      (computableInPolyTime_gmwCopy2 hφ hopened))).bool_and'
    (computableInPolyTime_verifyCommitments hg hs hm hφ hr hflags hcommit hopened hseeds)

@[fun_prop]
theorem isOraclePPTOn_gmwVerifier {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF) :
    IsOraclePPTOn (encPair encUnary enc) encBool
      (fun p : ℕ × α => gmwVerifier generator length f p.1 p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  let e0 := encPair encUnary enc; let e1 := encPair e0 encBits
  let e2 := encPair e1 encBits; let e3 := encPair e2 encBits
  have hs0 : ComputableInPolyTime (fun p : ℕ × α => p.1 + 7) e0 encUnary :=
    (ComputableInPolyTime.fst encUnary enc).unary_add' (.const 7)
  have hm0 : ComputableInPolyTime (fun p : ℕ × α => length (p.1 + 7)) e0 encUnary :=
    hlength.comp hs0
  have hφ0 : ComputableInPolyTime (fun p : ℕ × α => f p.2) e0 encCNF :=
    hf.comp (.snd encUnary enc)
  have hK0 : ComputableInPolyTime (fun p : ℕ × α => totalLen (f p.2)) e0 encUnary :=
    computableInPolyTime_totalLen hφ0
  dsimp only [gmwVerifier]
  apply IsOraclePPTOn.bind_with hm0.sampleList.isOraclePPTOn
  apply IsOraclePPTOn.bind_with (IsOraclePPTOn.query_take' () (.snd e0 encBits)
    ((hK0.comp (.fst e0 encBits)).unary_mul' (hm0.comp (.fst e0 encBits))))
  apply IsOraclePPTOn.bind_with (ComputableInPolyTime.const 3).sampleList.isOraclePPTOn
  have hp3_0 := ((ComputableInPolyTime.fst e2 encBits).fst').fst'
  simp only [bind_pure_comp]
  apply IsOraclePPTOn.map_with' (IsOraclePPTOn.query_take' () (.snd e2 encBits)
    ((hK0.comp hp3_0).unary_mul' ((hs0.comp hp3_0).unary_add' (.const 1))))
  have hp4_3 := ComputableInPolyTime.fst e3 encBits; have hp4_2 := hp4_3.fst'
  have hp4_1 := hp4_2.fst'; have hp4_0 := hp4_1.fst'
  exact computableInPolyTime_verifyTranscript hg (hs0.comp hp4_0) (hm0.comp hp4_0) (hφ0.comp hp4_0)
    hp4_1.snd' hp4_2.snd' hp4_3.snd' (.snd e3 encBits)

/-! ### PPT certificates for `runTwoRound` and honest interaction -/

/-- The state of `runTwoRound`: the round counter in unary, then the recorded challenge as a bit
word. The round counter is framed. -/
enc_structure encTwoRoundState : TwoRoundState where
  round : encUnary, challenge : encBits

/-- The prover's coins, as sampled for the honest prover by `sampleHonestCoins` or for the simulator
by `gmwSampleSimCoins`: the committed bits as a bit word, then the list of commitment seeds, each a
bit word. The bits are framed, and so is each seed. -/
enc_structure encProverCoins : ProverCoins where
  bits : encBits, seeds : (encList encBits)

theorem isPPTOn_runTwoRound {α β Caller : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    {prepare : Caller → ℕ × α × List Bool} {reply1 reply2 : Caller × List Bool → List Bool}
    {bound : Caller → ℕ}
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun (n, a, z) => Vstar n a z))
    (hprep : ComputableInPolyTime prepare input (encInstanceAuxInput enc))
    (hr1 : ComputableInPolyTime reply1 (encPair input encBits) encBits)
    (hr2 : ComputableInPolyTime reply2 (encPair input encBits) encBits)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hle1 : ∀ c q, (reply1 (c, q)).length ≤ bound c)
    (hle2 : ∀ c q, (reply2 (c, q)).length ≤ bound c) :
    IsPPTOn input (encPair encB encTwoRoundState)
      (fun c => runTwoRound (fun q => reply1 (c, q)) (fun q => reply2 (c, q))
        (Vstar (prepare c).1 (prepare c).2.1 (prepare c).2.2) .init) := by
  have hlen_state : ∀ s : TwoRoundState, s.round ≤ 2 → s.challenge.length = 3 →
      (encTwoRoundState s).length ≤ 9 := by
    intro s hs1 hs2
    simp only [encTwoRoundState_apply, encTwoRoundStateFields, length_encPair, encUnary_apply,
      List.length_replicate, encBits_apply, hs2]; omega
  have hc := ComputableInPolyTime.fst input
    (encPair (encPair (encFinEnum Unit) encBits) encTwoRoundState)
  have hqs := ComputableInPolyTime.snd input
    (encPair (encPair (encFinEnum Unit) encBits) encTwoRoundState)
  have hq := hqs.fst'.snd'; have hs := hqs.snd'
  have hround := encTwoRoundState_round_polyTime hs
  have hrow := (ComputableInPolyTime.const 3).bitsRowWithInput (.const 0) hq
  refine hV.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (stateEncoding := encTwoRoundState)
    (handler := fun c q s =>
      pure (twoRoundStep (fun x => reply1 (c, x)) (fun x => reply2 (c, x)) q.2 s))
    (prepare := prepare) (initial := fun _ => .init)
    (resources := fun c _ => bound c + 9) hprep.tidy
    (((hround.beq (.const 0)).ite'
      ((hr1.comp (hc.prod hq)).prod
        (encTwoRoundState_mk_polyTime (.const 1) (encTwoRoundState_challenge_polyTime hs)))
      ((hround.beq (.const 1)).ite'
        ((hr2.comp (hc.prod hrow)).prod (encTwoRoundState_mk_polyTime (.const 2) hrow))
        ((ComputableInPolyTime.const []).prod hs))).isPPTOn)
    (ComputableInPolyTime.const TwoRoundState.init).tidy
    (fun _ s => s.round ≤ 2 ∧ s.challenge.length = 3) (fun _ => ⟨Nat.zero_le _, rfl⟩)
    ((hbound.comp (.fst input encBits)).unary_add' (.const 9)).tidy
    (fun c request state hstate result hresult => ?_)
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hresult
  subst hresult; dsimp only [twoRoundStep]
  split_ifs with h0 h1
  · dsimp only; exact ⟨⟨by omega, hstate.2⟩, (hle1 c request.2).trans (by omega),
      (hlen_state ⟨1, state.challenge⟩ (Nat.le_succ 1) hstate.2).trans (by omega)⟩
  · dsimp only; exact ⟨⟨by omega, BitString.length_listRow 3 0 request.2⟩,
      (hle2 c _).trans (by omega), (hlen_state ⟨2, BitString.listRow 3 0 request.2⟩ le_rfl
        (BitString.length_listRow 3 0 request.2)).trans (by omega)⟩
  · dsimp only; exact ⟨hstate, by simp, (hlen_state state hstate.1 hstate.2).trans (by omega)⟩

@[fun_prop]
theorem isPPTOn_runTwoRound_prover {α β Caller : Type} {enc : α ↪ List Bool}
    {encB : β ↪ List Bool} {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    {generator : List Bool → List Bool} {n s m : Caller → ℕ} {a : Caller → α}
    {z : Caller → List Bool} {φ : Caller → CNF ℕ}
    {openFlags bits ch_guess : Caller → List Bool} {seeds pads : Caller → List (List Bool)}
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun (n, a, z) => Vstar n a z))
    (hg : ComputableInPolyTime generator encBits encBits)
    (hn : ComputableInPolyTime n input encUnary) (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (ha : ComputableInPolyTime a input enc)
    (hz : ComputableInPolyTime z input encBits) (hφ : ComputableInPolyTime φ input encCNF)
    (hopen : ComputableInPolyTime openFlags input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (hch : ComputableInPolyTime ch_guess input encBits)
    (hseeds : ComputableInPolyTime seeds input (encList encBits))
    (hpads : ComputableInPolyTime pads input (encList encBits)) :
    IsPPTOn input (encPair encB encTwoRoundState)
      (fun c => runTwoRound
        (fun r => proverReply1 generator (m c) r (openFlags c) (bits c) (seeds c) (pads c))
        (fun _ => proverReply2 (s c) (φ c) (ch_guess c) (bits c) (seeds c))
        (Vstar (n c) (a c) (z c)) .init) := by
  have hfst := ComputableInPolyTime.fst input encBits
  have hbits_len := hbits.length_bits_comp
  refine isPPTOn_runTwoRound hV (prepare := fun c => (n c, a c, z c))
    (reply1 := fun p => proverReply1 generator (m p.1) p.2 (openFlags p.1)
      (bits p.1) (seeds p.1) (pads p.1))
    (reply2 := fun p => proverReply2 (s p.1) (φ p.1) (ch_guess p.1) (bits p.1) (seeds p.1))
    (bound := fun c => (bits c).length * m c + (bits c).length * (s c + 1))
    (hn.prod (ha.prod hz))
    (computableInPolyTime_proverReply1 hg (hm.comp hfst) (.snd input encBits)
      (hopen.comp hfst) (hbits.comp hfst) (hseeds.comp hfst) (hpads.comp hfst))
    (computableInPolyTime_proverReply2 (hs.comp hfst) (hφ.comp hfst) (hch.comp hfst)
      (hbits.comp hfst) (hseeds.comp hfst))
    ((hbits_len.unary_mul' hm).unary_add' (hbits_len.unary_mul' (hs.unary_add' (.const 1))))
    (fun c q => by dsimp only; exact (List.length_take_le _ _).trans (by omega))
    (fun c q => by dsimp only; rw [length_proverReply2_any]; omega)

/-! ### GMW zero-knowledge simulator and its PPT certificate -/

@[fun_prop]
theorem computableInPolyTime_firstSuccess {α β : Type} {input : α ↪ List Bool}
    {enc : β ↪ List Bool} {d : α → β} {attempts : α → List (Option β)}
    (hd : ComputableInPolyTime d input enc)
    (ha : ComputableInPolyTime attempts input (encList (encOption enc))) :
    ComputableInPolyTime (fun a => firstSuccess (d a) (attempts a)) input enc :=
  let hfilt := (ComputableInPolyTime.headD (encA := encOption enc) none).comp'
    (ha.filterWithInput
      (ComputableTidilyInPolyTime.snd input (encOption enc)).optionIsSome.computableInPolyTime)
  (hfilt.tidy.optionGetDWithInput hd.tidy).computableInPolyTime

@[fun_prop]
theorem computableInPolyTime_acceptGuess {α β : Type} {input : α ↪ List Bool}
    {encB : β ↪ List Bool} {ch_guess : α → List Bool} {result : α → β × TwoRoundState}
    (hch : ComputableInPolyTime ch_guess input encBits)
    (hres : ComputableInPolyTime result input (encPair encB encTwoRoundState)) :
    ComputableInPolyTime (fun a => acceptGuess (ch_guess a) (result a)) input (encOption encB) := by
  unfold acceptGuess
  exact ((encTwoRoundState_challenge_polyTime hres.snd').beq hch).ite'
    ((ComputableInPolyTime.optionSome encB).comp hres.fst') (.const none)

private theorem isPPTOn_sampleThreeAndSeeds {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {combine : α → List Bool → List Bool → List Bool → List Bool}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hcomb : ComputableInPolyTime
      (fun p : ((α × List Bool) × List Bool) × List Bool => combine p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair input encBits) encBits) encBits) encBits) :
    IsPPTOn input encProverCoins
      (fun a => do
        let r₀ ← BitString.sampleList (φ a).vars.length
        let r₁ ← BitString.sampleList (φ a).vars.length
        let r₂ ← BitString.sampleList (φ a).vars.length
        let seeds ← OracleComp.replicate (totalLen (φ a)) (BitString.sampleList (s a))
        return ⟨combine a r₀ r₁ r₂, seeds⟩) := by
  have hvars := SAT.computableInPolyTime_vars_length hφ
  have htotal := computableInPolyTime_totalLen hφ
  let e1 := encPair input encBits; let e2 := encPair e1 encBits; let e3 := encPair e2 encBits
  have hfst1 := ComputableInPolyTime.fst input encBits
  have hfst2 := (ComputableInPolyTime.fst e1 encBits).trans hfst1
  have hfst3 := (ComputableInPolyTime.fst e2 encBits).trans hfst2
  apply IsPPTOn.bind_with hvars.sampleList
  apply IsPPTOn.bind_with (hvars.comp hfst1).sampleList
  apply IsPPTOn.bind_with (hvars.comp hfst2).sampleList
  simp only [bind_pure_comp]
  exact ((hs.comp hfst3).sampleList.replicate (htotal.comp hfst3)).map_with
    (encProverCoins_mk_polyTime (hcomb.comp (.fst e3 (encList encBits)))
      (.snd e3 (encList encBits)))

/-- Sample the GMW simulator's random strings and commitment seeds for a guessed challenge
`ch_guess`; the committed bits are `simBits φ ch_guess r₀ r₁ r₂`. -/
noncomputable def gmwSampleSimCoins (s : ℕ) (φ : CNF ℕ) (ch_guess : List Bool) :
    ProbComp ProverCoins := do
  let r₀ ← BitString.sampleList φ.vars.length
  let r₁ ← BitString.sampleList φ.vars.length
  let r₂ ← BitString.sampleList φ.vars.length
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  return ⟨simBits φ ch_guess r₀ r₁ r₂, seeds⟩

@[fun_prop]
theorem isPPTOn_gmwSampleSimCoins {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {ch_guess : α → List Bool}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hch : ComputableInPolyTime ch_guess input encBits) :
    IsPPTOn input encProverCoins (fun a => gmwSampleSimCoins (s a) (φ a) (ch_guess a)) := by
  let e1 := encPair input encBits; let e2 := encPair e1 encBits; let e3 := encPair e2 encBits
  have hp2 := ComputableInPolyTime.fst e2 encBits; have hp1 := hp2.fst'; have hp0 := hp1.fst'
  exact isPPTOn_sampleThreeAndSeeds hs hφ
    (computableInPolyTime_simBits (hφ.comp hp0) (hch.comp hp0) hp1.snd' hp2.snd' (.snd e2 encBits))

/-- Run one simulated GMW attempt on `prog` with pre-sampled unopened pads `pads`, without any
witness: guess the challenge, commit to `simBits` for that guess, and return the verifier's output
when its challenge equals the guess. -/
noncomputable def gmwSimWithPads {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (prog : WordOracleComp Unit β) (pads : List (List Bool)) :
    ProbComp (Option β) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← gmwSampleSimCoins s φ ch_guess
  acceptGuess ch_guess <$> runTwoRound
    (fun r => proverReply1 generator m r (allOpenFlags φ ch_guess coins.bits) coins.bits
      coins.seeds pads)
    (fun _ => proverReply2 s φ ch_guess coins.bits coins.seeds)
    prog .init

/-- One attempt of the GMW zero-knowledge simulator on `prog`, without any witness. -/
noncomputable def gmwSimAttempt {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (prog : WordOracleComp Unit β) : ProbComp (Option β) := do
  let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
  gmwSimWithPads generator s m φ prog pads

/-- The GMW zero-knowledge simulator: run `gmwSimAttempt` `n + 1` times and return the first
successful view, or `[]` when every attempt failed. -/
noncomputable def gmwSimulator {α : Type} (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (f : α → CNF ℕ) (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (n : ℕ) (a : α) (z : List Bool) : ProbComp (List Bool) :=
  firstSuccess [] <$> OracleComp.replicate (n + 1)
    (gmwSimAttempt generator (n + 7) (length (n + 7)) (f a) (Vstar n a z))

theorem isPPTOn_gmwSimWithPads {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length) (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encPair (encInstanceAuxInput enc) (encList encBits)) (encOption encB)
      (fun p : (ℕ × α × List Bool) × List (List Bool) =>
        gmwSimWithPads generator (p.1.1 + 7) (length (p.1.1 + 7))
          (f p.1.2.1) (Vstar p.1.1 p.1.2.1 p.1.2.2) p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  let e0 := encPair (encPair encUnary (encPair enc encBits)) (encList encBits)
  let e1 := encPair e0 encBits; let e2 := encPair e1 encProverCoins
  have hs0 : ComputableInPolyTime (fun p : (ℕ × α × List Bool) × List (List Bool) => p.1.1 + 7)
      e0 encUnary := ((ComputableInPolyTime.fst _ (encList encBits)).fst').unary_add' (.const 7)
  have hφ0 : ComputableInPolyTime (fun p : (ℕ × α × List Bool) × List (List Bool) => f p.1.2.1)
      e0 encCNF := hf.comp (((ComputableInPolyTime.fst _ (encList encBits)).snd').fst')
  dsimp only [gmwSimWithPads]
  apply IsPPTOn.bind_with (ComputableInPolyTime.const 3).sampleList
  have hfst1 := ComputableInPolyTime.fst e0 encBits
  apply IsPPTOn.bind_with
    (isPPTOn_gmwSampleSimCoins (hs0.comp hfst1) (hφ0.comp hfst1) (.snd e0 encBits))
  have hp1 := ComputableInPolyTime.fst e1 encProverCoins
  have hp0 := hp1.fst'; have hch := hp1.snd'
  have hcoins := ComputableInPolyTime.snd e1 encProverCoins
  have hφ2 := hφ0.comp hp0; have hbits := encProverCoins_bits_polyTime hcoins
  apply IsPPTOn.map_with (isPPTOn_runTwoRound_prover hV hg hp0.fst'.fst' (hs0.comp hp0)
    (hlength.comp (hs0.comp hp0)) hp0.fst'.snd'.fst' hp0.fst'.snd'.snd' hφ2
    (computableInPolyTime_allOpenFlags hφ2 hch hbits) hbits hch
    (encProverCoins_seeds_polyTime hcoins) hp0.snd')
  let eOut := encPair encB encTwoRoundState
  exact computableInPolyTime_acceptGuess ((ComputableInPolyTime.fst e2 eOut).fst').snd'
    (ComputableInPolyTime.snd e2 eOut)

theorem isPPTOn_gmwSimAttempt {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length) (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encInstanceAuxInput enc) (encOption encB)
      (fun p : ℕ × α × List Bool =>
        gmwSimAttempt generator (p.1 + 7) (length (p.1 + 7))
          (f p.2.1) (Vstar p.1 p.2.1 p.2.2)) := by
  have hlength := PRG.polyTime_length hg hlen
  exact IsPPTOn.bind_with
    (((hlength.comp ((ComputableInPolyTime.fst encUnary (encPair enc encBits)).unary_add'
        (.const 7))).sampleList).replicate
      (computableInPolyTime_totalLen
        (hf.comp ((ComputableInPolyTime.snd encUnary (encPair enc encBits)).fst'))))
    (isPPTOn_gmwSimWithPads hg hlen hf hV)

theorem isPPTOn_gmwSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length) (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encBits (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encInstanceAuxInput enc) encBits
      (fun (n, a, z) => gmwSimulator generator length f Vstar n a z) :=
  ((isPPTOn_gmwSimAttempt hg hlen hf hV).replicate
    ((ComputableInPolyTime.fst encUnary (encPair enc encBits)).unary_add' (.const 1))).map
    (computableInPolyTime_firstSuccess (.const []) .id')

@[fun_prop]
theorem computableInPolyTime_honestReply1 {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {m : α → ℕ} {φ : α → CNF ℕ}
    {coins : α → ProverCoins} {r : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hm : ComputableInPolyTime m input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hcoins : ComputableInPolyTime coins input encProverCoins)
    (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a => honestReply1 generator (m a) (φ a) (coins a) (r a))
      input encBits :=
  computableInPolyTime_proverReply1 hg hm hr
    ((ComputableInPolyTime.bitsReplicate true).comp (computableInPolyTime_totalLen hφ))
    (encProverCoins_bits_polyTime hcoins) (encProverCoins_seeds_polyTime hcoins) (.const [])

@[fun_prop]
theorem computableInPolyTime_honestReply2 {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {coins : α → ProverCoins} {ch : α → List Bool}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hcoins : ComputableInPolyTime coins input encProverCoins)
    (hch : ComputableInPolyTime ch input encBits) :
    ComputableInPolyTime (fun a => honestReply2 (s a) (φ a) (coins a) (ch a)) input encBits :=
  computableInPolyTime_proverReply2 hs hφ hch (encProverCoins_bits_polyTime hcoins)
    (encProverCoins_seeds_polyTime hcoins)

@[fun_prop]
theorem isPPTOn_runTwoRound_honest {α Caller : Type} {enc : α ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {generator : List Bool → List Bool} {n s m : Caller → ℕ} {a : Caller → α}
    {z : Caller → List Bool} {φ : Caller → CNF ℕ} {coins : Caller → ProverCoins}
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encBits (fun (n, a, z) => Vstar n a z))
    (hg : ComputableInPolyTime generator encBits encBits)
    (hn : ComputableInPolyTime n input encUnary) (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (ha : ComputableInPolyTime a input enc)
    (hz : ComputableInPolyTime z input encBits) (hφ : ComputableInPolyTime φ input encCNF)
    (hcoins : ComputableInPolyTime coins input encProverCoins) :
    IsPPTOn input (encPair encBits encTwoRoundState)
      (fun c => runTwoRound (honestReply1 generator (m c) (φ c) (coins c))
        (honestReply2 (s c) (φ c) (coins c)) (Vstar (n c) (a c) (z c)) .init) := by
  have hfst := ComputableInPolyTime.fst input encBits
  have hbits_len := (encProverCoins_bits_polyTime hcoins).length_bits_comp
  refine isPPTOn_runTwoRound hV (prepare := fun c => (n c, a c, z c))
    (reply1 := fun p => honestReply1 generator (m p.1) (φ p.1) (coins p.1) p.2)
    (reply2 := fun p => honestReply2 (s p.1) (φ p.1) (coins p.1) p.2)
    (bound := fun c => (coins c).bits.length * m c + (coins c).bits.length * (s c + 1))
    (hn.prod (ha.prod hz))
    (computableInPolyTime_honestReply1 hg (hm.comp hfst) (hφ.comp hfst)
      (hcoins.comp hfst) (.snd input encBits))
    (computableInPolyTime_honestReply2 (hs.comp hfst) (hφ.comp hfst)
      (hcoins.comp hfst) (.snd input encBits))
    ((hbits_len.unary_mul' hm).unary_add' (hbits_len.unary_mul' (hs.unary_add' (.const 1))))
    (fun c q => by dsimp only [honestReply1]; exact (List.length_take_le _ _).trans (by omega))
    (fun c q => by dsimp only [honestReply2]; rw [length_proverReply2_any]; omega)

@[fun_prop]
theorem isPPTOn_sampleHonestCoins {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {w : α → List Bool}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hw : ComputableInPolyTime w input encBits) :
    IsPPTOn input encProverCoins (fun a => sampleHonestCoins (s a) (φ a) (w a)) := by
  let e1 := encPair input encBits; let e2 := encPair e1 encBits; let e3 := encPair e2 encBits
  have hp2 := ComputableInPolyTime.fst e2 encBits; have hp1 := hp2.fst'; have hp0 := hp1.fst'
  exact isPPTOn_sampleThreeAndSeeds hs hφ
    (computableInPolyTime_realBits (hφ.comp hp0) (hw.comp hp0) hp1.snd' hp2.snd' (.snd e2 encBits))

theorem isPPTOn_gmwInteract {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length) (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encBits (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encInstanceWitnessAuxInput enc) encBits
      (fun (n, a, w, z) =>
        gmwInteract generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z)) := by
  have hlength := PRG.polyTime_length hg hlen
  let e0 := encPair encUnary (encPair enc (encPair encBits encBits))
  have hs0 : ComputableInPolyTime (fun p : ℕ × α × List Bool × List Bool => p.1 + 7)
      e0 encUnary :=
    (ComputableInPolyTime.fst encUnary (encPair enc (encPair encBits encBits))).unary_add'
      (.const 7)
  have hφ0 : ComputableInPolyTime (fun p : ℕ × α × List Bool × List Bool => f p.2.1)
      e0 encCNF :=
    hf.comp ((ComputableInPolyTime.snd encUnary (encPair enc (encPair encBits encBits))).fst')
  have hw0 : ComputableInPolyTime (fun p : ℕ × α × List Bool × List Bool => p.2.2.1)
      e0 encBits :=
    ((ComputableInPolyTime.snd encUnary (encPair enc (encPair encBits encBits))).snd').fst'
  dsimp only [gmwInteract]
  apply IsPPTOn.bind_with (isPPTOn_sampleHonestCoins hs0 hφ0 hw0)
  simp only [bind_pure_comp]
  have hp0 := ComputableInPolyTime.fst e0 encProverCoins
  exact (isPPTOn_runTwoRound_honest hV hg
    hp0.fst' (hs0.comp hp0) (hlength.comp (hs0.comp hp0))
    hp0.snd'.fst' hp0.snd'.snd'.snd' (hφ0.comp hp0) (.snd e0 encProverCoins)).map
    (.fst encBits encTwoRoundState)

end Cslib.Crypto.GMW
