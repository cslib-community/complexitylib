/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.OracleSimulation
public import Complexity.Crypto.Computational.GMW.Protocol
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Tactic.PPT

/-!
# Polynomial-time and PPT certificates for the 3-copy GMW protocol

This module registers `@[fun_prop]` polynomial-time and strict-(oracle-)PPT certificates for the
3-copy masked-3SAT GMW protocol gadgets defined in `Complexity.Crypto.Computational.GMW.Protocol`,
proves that `runTwoRound` preserves strict PPT when driven by polynomial-time round functions and a
strict oracle PPT verifier (`isPPTOn_runTwoRound`), defines the zero-knowledge simulator
`gmwSimulator` (via `gmwFirstSuccess`, `gmwSampleSimCoins`, `gmwSimWithPads`, `gmwSimAttempt`), and
certifies:

* `isOraclePPTOn_gmwVerifier`: the honest verifier `gmwVerifier` is uniform strict oracle PPT;
* `isPPTOn_gmwInteract`: running any uniform strict oracle PPT verifier against the honest prover is
  uniform strict PPT;
* `isPPTOn_gmwSimulator`: the GMW zero-knowledge simulator `gmwSimulator` is uniform strict PPT.

## Main definitions

* `Cslib.Crypto.GMW.gmwFirstSuccess`: extracts the payload of the first successful simulation
  attempt (`true :: out`) from a list of attempts.
* `Cslib.Crypto.GMW.gmwSampleSimCoins`, `Cslib.Crypto.GMW.gmwSimWithPads`,
  `Cslib.Crypto.GMW.gmwSimAttempt`: single-attempt GMW simulator components.
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

open Probability Complexity Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime

/-! Tidy views of the plain `SAT` certificates, for tidy `fun_prop` below. -/

@[local fun_prop]
private theorem computableTidilyInPolyTime_vars :
    ComputableTidilyInPolyTime (CNF.vars (V := ℕ)) encCNF (encList encNat) :=
  (ComputableInPolyTime.tidy (SAT.computableInPolyTime_vars))

@[local fun_prop]
private theorem computableTidilyInPolyTime_clause_length
    {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => (c a).length) input encUnary :=
  (ComputableInPolyTime.tidy (SAT.computableInPolyTime_clause_length (.of_tidy hc)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_length
    {α : Type} {input : α ↪ List Bool} {φ : α → CNF ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => (φ a).length) input encUnary :=
  (ComputableInPolyTime.tidy (SAT.computableInPolyTime_length (.of_tidy hφ)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_vars_length
    {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => (φ a).vars.length) input encUnary :=
  (ComputableInPolyTime.tidy (SAT.computableInPolyTime_vars_length (.of_tidy hφ)))

/-! ### Polynomial-time certificates for protocol gadgets -/

private theorem computableTidilyInPolyTime_clauseLitVar (i : ℕ) {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => ((c a).getD i (0, false)).1) input encNat := by
  have hget : ComputableTidilyInPolyTime (fun a => (c a).getD i (0, false))
      input (encPair encNat encBool) :=
    (listGetD (0, false)).comp (hc.prod (const i))
  exact (fst encNat encBool).comp hget

private theorem computableTidilyInPolyTime_clauseLitPol (i : ℕ) {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => ((c a).getD i (0, false)).2) input encBool := by
  have hget : ComputableTidilyInPolyTime (fun a => (c a).getD i (0, false))
      input (encPair encNat encBool) :=
    (listGetD (0, false)).comp (hc.prod (const i))
  exact (snd encNat encBool).comp hget

@[fun_prop]
theorem computableTidilyInPolyTime_gmwBit0Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableTidilyInPolyTime t input encUnary) :
    ComputableTidilyInPolyTime (fun a => gmwBit0Of8 (t a)) input encBool := by
  dsimp only [gmwBit0Of8]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_gmwBit1Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableTidilyInPolyTime t input encUnary) :
    ComputableTidilyInPolyTime (fun a => gmwBit1Of8 (t a)) input encBool := by
  dsimp only [gmwBit1Of8]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_gmwBit2Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableTidilyInPolyTime t input encUnary) :
    ComputableTidilyInPolyTime (fun a => gmwBit2Of8 (t a)) input encBool := by
  dsimp only [gmwBit2Of8]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_gmwActiveIdx {α : Type} {input : α ↪ List Bool}
    {b₀ b₁ b₂ : α → Bool}
    (hb₀ : ComputableTidilyInPolyTime b₀ input encBool)
    (hb₁ : ComputableTidilyInPolyTime b₁ input encBool)
    (hb₂ : ComputableTidilyInPolyTime b₂ input encBool) :
    ComputableTidilyInPolyTime (fun a => gmwActiveIdx (b₀ a) (b₁ a) (b₂ a)) input encUnary := by
  dsimp only [gmwActiveIdx]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_clauseEvalBits {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ} {b₀ b₁ b₂ : α → Bool}
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool)))
    (hb₀ : ComputableTidilyInPolyTime b₀ input encBool)
    (hb₁ : ComputableTidilyInPolyTime b₁ input encBool)
    (hb₂ : ComputableTidilyInPolyTime b₂ input encBool) :
    ComputableTidilyInPolyTime (fun a => clauseEvalBits (c a) (b₀ a) (b₁ a) (b₂ a))
      input encBool := by
  have hp0 := computableTidilyInPolyTime_clauseLitPol 0 hc
  have hp1 := computableTidilyInPolyTime_clauseLitPol 1 hc
  have hp2 := computableTidilyInPolyTime_clauseLitPol 2 hc
  dsimp only [clauseEvalBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_varBit {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {vec : α → List Bool} {v : α → ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hvec : ComputableTidilyInPolyTime vec input encBits)
    (hv : ComputableTidilyInPolyTime v input encNat) :
    ComputableTidilyInPolyTime (fun a => varBit (φ a) (vec a) (v a)) input encBool := by
  dsimp only [varBit]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_clauseTableRow {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {m : α → List Bool} {c : α → Clause ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hm : ComputableTidilyInPolyTime m input encBits)
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => clauseTableRow (φ a) (m a) (c a)) input encBits := by
  have hv0 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 0 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 0 (hc.comp (fst input encUnary))
  have hv1 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 1 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 1 (hc.comp (fst input encUnary))
  have hv2 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 2 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 2 (hc.comp (fst input encUnary))
  dsimp only [clauseTableRow]
  exact mapToBitsWithInput (range.comp (const 8)) (by fun_prop)

@[fun_prop]
theorem computableTidilyInPolyTime_clauseActiveRow {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {v : α → List Bool} {c : α → Clause ℕ}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hv : ComputableTidilyInPolyTime v input encBits)
    (hc : ComputableTidilyInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableTidilyInPolyTime (fun a => clauseActiveRow (φ a) (v a) (c a)) input encBits := by
  have hv0 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 0 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 0 (hc.comp (fst input encUnary))
  have hv1 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 1 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 1 (hc.comp (fst input encUnary))
  have hv2 : ComputableTidilyInPolyTime (fun p : α × ℕ => ((c p.1).getD 2 (0, false)).1)
      (encPair input encUnary) encNat :=
    computableTidilyInPolyTime_clauseLitVar 2 (hc.comp (fst input encUnary))
  have heq (x y : ℕ) : decide (x = y) = (x == y) := Bool.eq_iff_iff.mpr (by simp)
  dsimp only [clauseActiveRow]
  simp only [heq]
  exact mapToBitsWithInput (range.comp (const 8)) (by fun_prop)

@[fun_prop]
theorem computableTidilyInPolyTime_tableBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {m : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hm : ComputableTidilyInPolyTime m input encBits) :
    ComputableTidilyInPolyTime (fun a => tableBits (φ a) (m a)) input encBits := by
  dsimp only [tableBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_activeTableFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {v : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hv : ComputableTidilyInPolyTime v input encBits) :
    ComputableTidilyInPolyTime (fun a => activeTableFlags (φ a) (v a)) input encBits := by
  dsimp only [activeTableFlags]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_copyLen {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => copyLen (φ a)) input encUnary := by
  dsimp only [copyLen]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_totalLen {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun a => totalLen (φ a)) input encUnary := by
  dsimp only [totalLen]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_mPart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => mPart (φ a) (copy a)) input encBits := by
  dsimp only [mPart]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_vPart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => vPart (φ a) (copy a)) input encBits := by
  dsimp only [vPart]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_tablePart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => tablePart (φ a) (copy a)) input encBits := by
  dsimp only [tablePart]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_realCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {w m : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hw : ComputableTidilyInPolyTime w input encBits)
    (hm : ComputableTidilyInPolyTime m input encBits) :
    ComputableTidilyInPolyTime (fun a => realCopyBits (φ a) (w a) (m a)) input encBits := by
  dsimp only [realCopyBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_simCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {rand : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hb : ComputableTidilyInPolyTime b input encBool)
    (hrand : ComputableTidilyInPolyTime rand input encBits) :
    ComputableTidilyInPolyTime (fun a => simCopyBits (φ a) (b a) (rand a)) input encBits := by
  dsimp only [simCopyBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_copyOpenFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hb : ComputableTidilyInPolyTime b input encBool)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => copyOpenFlags (φ a) (b a) (copy a)) input encBits := by
  dsimp only [copyOpenFlags]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_verifyCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {copy : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hb : ComputableTidilyInPolyTime b input encBool)
    (hcopy : ComputableTidilyInPolyTime copy input encBits) :
    ComputableTidilyInPolyTime (fun a => verifyCopyBits (φ a) (b a) (copy a)) input encBool := by
  dsimp only [verifyCopyBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_gmwCopy0 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hbits : ComputableTidilyInPolyTime bits input encBits) :
    ComputableTidilyInPolyTime (fun a => gmwCopy0 (φ a) (bits a)) input encBits := by
  dsimp only [gmwCopy0]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_gmwCopy1 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hbits : ComputableTidilyInPolyTime bits input encBits) :
    ComputableTidilyInPolyTime (fun a => gmwCopy1 (φ a) (bits a)) input encBits := by
  dsimp only [gmwCopy1]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_gmwCopy2 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hbits : ComputableTidilyInPolyTime bits input encBits) :
    ComputableTidilyInPolyTime (fun a => gmwCopy2 (φ a) (bits a)) input encBits := by
  dsimp only [gmwCopy2]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_realBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {w m₀ m₁ m₂ : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hw : ComputableTidilyInPolyTime w input encBits)
    (hm₀ : ComputableTidilyInPolyTime m₀ input encBits)
    (hm₁ : ComputableTidilyInPolyTime m₁ input encBits)
    (hm₂ : ComputableTidilyInPolyTime m₂ input encBits) :
    ComputableTidilyInPolyTime (fun a => realBits (φ a) (w a) (m₀ a) (m₁ a) (m₂ a))
      input encBits := by
  dsimp only [realBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_simBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {ch r₀ r₁ r₂ : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hch : ComputableTidilyInPolyTime ch input encBits)
    (hr₀ : ComputableTidilyInPolyTime r₀ input encBits)
    (hr₁ : ComputableTidilyInPolyTime r₁ input encBits)
    (hr₂ : ComputableTidilyInPolyTime r₂ input encBits) :
    ComputableTidilyInPolyTime (fun a => simBits (φ a) (ch a) (r₀ a) (r₁ a) (r₂ a))
      input encBits := by
  dsimp only [simBits]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_allOpenFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {ch bits : α → List Bool}
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hch : ComputableTidilyInPolyTime ch input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits) :
    ComputableTidilyInPolyTime (fun a => allOpenFlags (φ a) (ch a) (bits a))
      input encBits := by
  dsimp only [allOpenFlags]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_proverReply1 {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {m : α → ℕ}
    {r openFlags bits : α → List Bool} {seeds pads : α → List (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hopen : ComputableTidilyInPolyTime openFlags input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits)
    (hseeds : ComputableTidilyInPolyTime seeds input (encList encBits))
    (hpads : ComputableTidilyInPolyTime pads input (encList encBits)) :
    ComputableTidilyInPolyTime
      (fun a => proverReply1 generator (m a) (r a) (openFlags a) (bits a) (seeds a) (pads a))
      input encBits := by
  dsimp only [proverReply1]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_proverReply2 {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {ch bits : α → List Bool} {seeds : α → List (List Bool)}
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hch : ComputableTidilyInPolyTime ch input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits)
    (hseeds : ComputableTidilyInPolyTime seeds input (encList encBits)) :
    ComputableTidilyInPolyTime
      (fun a => proverReply2 (s a) (φ a) (ch a) (bits a) (seeds a))
      input encBits := by
  dsimp only [proverReply2]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_verifyCommitments {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {r flags commitReply openedBits openSeedsFlat : α → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hflags : ComputableTidilyInPolyTime flags input encBits)
    (hcommit : ComputableTidilyInPolyTime commitReply input encBits)
    (hopened : ComputableTidilyInPolyTime openedBits input encBits)
    (hseeds : ComputableTidilyInPolyTime openSeedsFlat input encBits) :
    ComputableTidilyInPolyTime
      (fun a => verifyCommitments generator (s a) (m a) (φ a) (r a) (flags a)
        (commitReply a) (openedBits a) (openSeedsFlat a))
      input encBool := by
  dsimp only [verifyCommitments]
  fun_prop

@[fun_prop]
theorem computableTidilyInPolyTime_verifyTranscript {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {r commitReply ch openReply : α → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hcommit : ComputableTidilyInPolyTime commitReply input encBits)
    (hch : ComputableTidilyInPolyTime ch input encBits)
    (hopen : ComputableTidilyInPolyTime openReply input encBits) :
    ComputableTidilyInPolyTime
      (fun a => verifyTranscript generator (s a) (m a) (φ a) (r a)
        (commitReply a) (ch a) (openReply a))
      input encBool := by
  dsimp only [verifyTranscript]
  fun_prop

@[fun_prop]
theorem isOraclePPTOn_gmwVerifier {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF) :
    IsOraclePPTOn (encPair encUnary enc) encBool
      (fun p : ℕ × α => gmwVerifier generator length f p.1 p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  dsimp only [gmwVerifier]
  fun_prop

/-! ### PPT certificates for `runTwoRound` and honest interaction -/

theorem isPPTOn_runTwoRound {α Caller : Type} {enc : α ↪ List Bool} {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {prepare : Caller → ℕ × α × List Bool}
    {reply1 reply2 : Caller × List Bool → List Bool}
    {bound : Caller → ℕ}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (hprep : ComputableTidilyInPolyTime prepare input (encPair encUnary (encPair enc encBits)))
    (hr1 : ComputableTidilyInPolyTime reply1 (encPair input encBits) encBits)
    (hr2 : ComputableTidilyInPolyTime reply2 (encPair input encBits) encBits)
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (hle1 : ∀ c q, (reply1 (c, q)).length ≤ bound c)
    (hle2 : ∀ c q, (reply2 (c, q)).length ≤ bound c) :
    IsPPTOn input (encPair encBits (encPair encUnary encBits))
      (fun c => runTwoRound (fun q => reply1 (c, q)) (fun q => reply2 (c, q))
        (Vstar (prepare c).1 (prepare c).2.1 (prepare c).2.2) (0, [false, false, false])) := by
  let stateEncoding : ℕ × List Bool ↪ List Bool := encPair encUnary encBits
  have hlen_state : ∀ s : ℕ × List Bool, s.1 ≤ 2 → s.2.length = 3 →
      (stateEncoding s).length ≤ 9 := by
    intro s hs1 hs2
    simp only [stateEncoding, length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply, hs2]
    omega
  refine hV.run_interpret_preprocess (stateEncoding := stateEncoding)
    (handler := fun c q s =>
      pure (twoRoundStep (fun x => reply1 (c, x)) (fun x => reply2 (c, x)) q.2 s))
    (prepare := prepare)
    (initial := fun _ => (0, [false, false, false]))
    (resources := fun c _ => bound c + 9)
    hprep
    (by dsimp only [twoRoundStep, stateEncoding]; fun_prop)
    (by dsimp only [stateEncoding]; fun_prop)
    (fun _ s => s.1 ≤ 2 ∧ s.2.length = 3)
    (fun _ => ⟨by omega, rfl⟩)
    (by fun_prop)
    (fun c request state hstate result hresult => ?_)
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hresult
  subst hresult
  dsimp only [twoRoundStep]
  split_ifs with h0 h1
  · dsimp only
    refine ⟨⟨by omega, hstate.2⟩, (hle1 c request.2).trans (by omega), ?_⟩
    exact (hlen_state (1, state.2) (by omega) hstate.2).trans (by omega)
  · dsimp only
    refine ⟨⟨by omega, BitString.length_listRow 3 0 request.2⟩,
      (hle2 c _).trans (by omega), ?_⟩
    exact (hlen_state (2, BitString.listRow 3 0 request.2)
      (by omega) (BitString.length_listRow 3 0 request.2)).trans (by omega)
  · dsimp only
    refine ⟨hstate, by simp, ?_⟩
    exact (hlen_state state hstate.1 hstate.2).trans (by omega)

@[fun_prop]
theorem isPPTOn_runTwoRound_prover {α Caller : Type} {enc : α ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {generator : List Bool → List Bool}
    {n s m : Caller → ℕ} {a : Caller → α} {z : Caller → List Bool}
    {φ : Caller → CNF ℕ}
    {openFlags bits ch_guess : Caller → List Bool}
    {seeds pads : Caller → List (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (ha : ComputableTidilyInPolyTime a input enc)
    (hz : ComputableTidilyInPolyTime z input encBits)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hopen : ComputableTidilyInPolyTime openFlags input encBits)
    (hbits : ComputableTidilyInPolyTime bits input encBits)
    (hch : ComputableTidilyInPolyTime ch_guess input encBits)
    (hseeds : ComputableTidilyInPolyTime seeds input (encList encBits))
    (hpads : ComputableTidilyInPolyTime pads input (encList encBits)) :
    IsPPTOn input (encPair encBits (encPair encUnary encBits))
      (fun c => runTwoRound
        (fun r => proverReply1 generator (m c) r (openFlags c) (bits c) (seeds c) (pads c))
        (fun _ => proverReply2 (s c) (φ c) (ch_guess c) (bits c) (seeds c))
        (Vstar (n c) (a c) (z c))
        (0, [false, false, false])) := by
  refine isPPTOn_runTwoRound hV
    (prepare := fun c => (n c, a c, z c))
    (reply1 := fun p => proverReply1 generator (m p.1) p.2 (openFlags p.1)
      (bits p.1) (seeds p.1) (pads p.1))
    (reply2 := fun p => proverReply2 (s p.1) (φ p.1) (ch_guess p.1) (bits p.1) (seeds p.1))
    (bound := fun c => (bits c).length * m c + (bits c).length * (s c + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun c q => by dsimp only; exact (List.length_take_le _ _).trans (by omega))
    (fun c q => by dsimp only; rw [length_proverReply2_any]; omega)

/-! ### GMW zero-knowledge simulator and its PPT certificate -/

/-- Extract the payload of the first successful GMW simulation attempt (`true :: out`), or `[]` if
all attempts failed (`[]`). -/
def gmwFirstSuccess (attempts : List (List Bool)) : List Bool :=
  ((attempts.filter (fun w => w.headD false)).headD []).tail

@[fun_prop]
theorem computableTidilyInPolyTime_gmwFirstSuccess {α : Type} {input : α ↪ List Bool}
    {attempts : α → List (List Bool)}
    (ha : ComputableTidilyInPolyTime attempts input (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => gmwFirstSuccess (attempts a)) input encBits := by
  dsimp only [gmwFirstSuccess]
  fun_prop

/-- Sample the GMW simulator's random strings and commitment seeds for a guessed challenge
`ch_guess`, returning `(simBits φ ch_guess r₀ r₁ r₂, seeds)`. -/
noncomputable def gmwSampleSimCoins (s : ℕ) (φ : CNF ℕ) (ch_guess : List Bool) :
    ProbComp (List Bool × List (List Bool)) := do
  let r₀ ← BitString.sampleList φ.vars.length
  let r₁ ← BitString.sampleList φ.vars.length
  let r₂ ← BitString.sampleList φ.vars.length
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  return (simBits φ ch_guess r₀ r₁ r₂, seeds)

@[fun_prop]
theorem isPPTOn_gmwSampleSimCoins {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {ch_guess : α → List Bool}
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hch : ComputableTidilyInPolyTime ch_guess input encBits) :
    IsPPTOn input (encPair encBits (encList encBits))
      (fun a => gmwSampleSimCoins (s a) (φ a) (ch_guess a)) := by
  dsimp only [gmwSampleSimCoins]
  ppt

/-- Run one simulated GMW attempt with pre-sampled unopened pads `pads` (without any witness). -/
noncomputable def gmwSimWithPads (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit (List Bool)) (pads : List (List Bool)) :
    ProbComp (List Bool) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← gmwSampleSimCoins s φ ch_guess
  let p ← runTwoRound
    (fun r => proverReply1 generator m r (allOpenFlags φ ch_guess coins.1) coins.1 coins.2 pads)
    (fun _ => proverReply2 s φ ch_guess coins.1 coins.2)
    prog (0, [false, false, false])
  return if p.2.2 == ch_guess then true :: p.1 else []

/-- One attempt of the GMW zero-knowledge simulator (without any witness). -/
noncomputable def gmwSimAttempt (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
  gmwSimWithPads generator s m φ prog pads

/-- The GMW zero-knowledge simulator: repeat `gmwSimAttempt` `n + 1` times and return the first
successful output (`gmwFirstSuccess`). -/
noncomputable def gmwSimulator {α : Type} (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (f : α → CNF ℕ) (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (n : ℕ) (a : α) (z : List Bool) : ProbComp (List Bool) :=
  gmwFirstSuccess <$> OracleComp.replicate (n + 1)
    (gmwSimAttempt generator (n + 7) (length (n + 7)) (f a) (Vstar n a z))

private theorem isPPTOn_gmwSimWithPads {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) (encList encBits)) encBits
      (fun p : (ℕ × α × List Bool) × List (List Bool) =>
        gmwSimWithPads generator (p.1.1 + 7) (length (p.1.1 + 7))
          (f p.1.2.1) (Vstar p.1.1 p.1.2.1 p.1.2.2) p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  dsimp only [gmwSimWithPads]
  ppt

private theorem isPPTOn_gmwSimAttempt {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool =>
        gmwSimAttempt generator (p.1 + 7) (length (p.1 + 7))
          (f p.2.1) (Vstar p.1 p.2.1 p.2.2)) := by
  have hlength := PRG.polyTime_length hg hlen
  have hpad := isPPTOn_gmwSimWithPads hg hlen hf hV
  dsimp only [gmwSimAttempt]
  ppt

theorem isPPTOn_gmwSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p : ℕ × α × List Bool =>
        gmwSimulator generator length f Vstar p.1 p.2.1 p.2.2) := by
  have hattempt := isPPTOn_gmwSimAttempt hg hlen hf hV
  dsimp only [gmwSimulator]
  ppt

@[local fun_prop]
private theorem computableTidilyInPolyTime_honestReply1 {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {m : α → ℕ} {φ : α → CNF ℕ}
    {coins : α → List Bool × List (List Bool)} {r : α → List Bool}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcoins : ComputableTidilyInPolyTime coins input (encPair encBits (encList encBits)))
    (hr : ComputableTidilyInPolyTime r input encBits) :
    ComputableTidilyInPolyTime
      (fun a => honestReply1 generator (m a) (φ a) (coins a) (r a))
      input encBits := by
  dsimp only [honestReply1]
  fun_prop

@[local fun_prop]
private theorem computableTidilyInPolyTime_honestReply2 {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ}
    {coins : α → List Bool × List (List Bool)} {ch : α → List Bool}
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcoins : ComputableTidilyInPolyTime coins input (encPair encBits (encList encBits)))
    (hch : ComputableTidilyInPolyTime ch input encBits) :
    ComputableTidilyInPolyTime
      (fun a => honestReply2 (s a) (φ a) (coins a) (ch a))
      input encBits := by
  dsimp only [honestReply2]
  fun_prop

@[local fun_prop]
private theorem isPPTOn_runTwoRound_honest {α Caller : Type} {enc : α ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {generator : List Bool → List Bool}
    {n s m : Caller → ℕ} {a : Caller → α} {z : Caller → List Bool}
    {φ : Caller → CNF ℕ} {coins : Caller → List Bool × List (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2))
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hs : ComputableTidilyInPolyTime s input encUnary)
    (hm : ComputableTidilyInPolyTime m input encUnary)
    (ha : ComputableTidilyInPolyTime a input enc)
    (hz : ComputableTidilyInPolyTime z input encBits)
    (hφ : ComputableTidilyInPolyTime φ input encCNF)
    (hcoins : ComputableTidilyInPolyTime coins input (encPair encBits (encList encBits))) :
    IsPPTOn input (encPair encBits (encPair encUnary encBits))
      (fun c => runTwoRound
        (honestReply1 generator (m c) (φ c) (coins c))
        (honestReply2 (s c) (φ c) (coins c))
        (Vstar (n c) (a c) (z c))
        (0, [false, false, false])) := by
  refine isPPTOn_runTwoRound hV
    (prepare := fun c => (n c, a c, z c))
    (reply1 := fun p => honestReply1 generator (m p.1) (φ p.1) (coins p.1) p.2)
    (reply2 := fun p => honestReply2 (s p.1) (φ p.1) (coins p.1) p.2)
    (bound := fun c => (coins c).1.length * m c + (coins c).1.length * (s c + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun c q => by dsimp only [honestReply1]; exact (List.length_take_le _ _).trans (by omega))
    (fun c q => by dsimp only [honestReply2]; rw [length_proverReply2_any]; omega)

theorem isPPTOn_gmwInteract {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableTidilyInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableTidilyInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary (encPair enc (encPair encBits encBits))) encBits
      (fun p : ℕ × α × List Bool × List Bool =>
        gmwInteract generator (p.1 + 7) (length (p.1 + 7)) (f p.2.1) p.2.2.1
          (Vstar p.1 p.2.1 p.2.2.2)) := by
  have hlength := PRG.polyTime_length hg hlen
  dsimp only [gmwInteract, sampleHonestCoins]
  ppt

end Cslib.Crypto.GMW
