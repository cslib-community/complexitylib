/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.TFNP.Subclasses
public import Complexity.Computability.Complexity.Problems.CircuitValue.Compilation
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Completeness of canonical total search problems

Uniform polynomial-time function families compile into circuit codes in polynomial time. This
proves completeness of `Pigeon`, `EndOfLine`, `Leaf` and `LocalOpt` for `PPP`, `PPAD`, `PPA` and
`PLS`, respectively, under `SearchReducible` across arbitrary encoded instance types.
The reductions preserve vertex witnesses. Local-search costs are compiled as fixed-width binary
words with leading zeros, preserving numerical values rather than merely the existence of optima.

## Main results

* `Cslib.Complexity.Pigeon_searchComplete`: `PPP` completeness.
* `Cslib.Complexity.EndOfLine_searchComplete`: `PPAD` completeness.
* `Cslib.Complexity.Leaf_searchComplete`: `PPA` completeness.
* `Cslib.Complexity.LocalOpt_searchComplete`: `PLS` completeness.

## References

* [D. S. Johnson, C. H. Papadimitriou, M. Yannakakis, *How easy is local
  search?*][JohnsonPapadimitriouYannakakis1988]
* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
* [P. Beame, S. Cook, J. Edmonds, R. Impagliazzo, T. Pitassi, *The relative complexity of NP search
  problems*][BeameEtAl1998]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-- Compile fixed-width function families exactly on their prescribed input cubes. -/
theorem exists_uniformCircuitCodes {n m : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits)
    (hlen : ∀ a u, u.length = n a → (F (a, u)).length = m a) :
    ∃ code : α → CircuitCode, ComputableInPolyTime code enc encCode ∧
      ∀ a u, u.length = n a → evalCircuitOutputs (code a) u = F (a, u) := by
  obtain ⟨circuits, hcode, hsem⟩ := CircuitValue.exists_uniformCircuitFamily hn hm hF
  refine ⟨fun a => (circuits a).code, hcode, fun a u hu => ?_⟩
  let x (i : Fin (n a)) := u.getD i.val false
  have hx : List.ofFn x = u := by
    apply List.ext_getElem (by simp [hu])
    intro i hi hj
    simp only [List.getElem_ofFn]
    exact List.getD_eq_getElem _ _ hj
  rw [← hx, evalCircuitOutputs_code]
  apply List.ext_getElem (by simp [hlen a _ (List.length_ofFn)])
  intro i hi hj
  simp only [List.getElem_ofFn]
  rw [hsem a x]
  exact List.getD_eq_getElem _ _ hj

private theorem exists_endomorphismCodes {n : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits)
    (hlen : ∀ a u, u.length = n a → (F (a, u)).length = n a) :
    ∃ code : α → CircuitCode, ComputableInPolyTime code enc encCode ∧
      ∀ a u, u.length = n a → evalCircuitCode (n a) (code a) u = F (a, u) := by
  obtain ⟨code, hcode, hsem⟩ := exists_uniformCircuitCodes hn hn
    hF hlen
  refine ⟨code, hcode, fun a u hu => ?_⟩
  rw [evalCircuitCode, hsem a u hu, padBits_of_length_eq (hlen a u hu)]

/-- A uniform polynomial-time pigeonhole family reduces to the canonical circuit problem. -/
theorem pigeonRel_searchReducible_Pigeon {n : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits)
    (hlen : ∀ a u, u.length = n a → (F (a, u)).length = n a) :
    SearchReducible enc encPigeon (pigeonRel n F) Pigeon := by
  obtain ⟨code, hcode, hsem⟩ := exists_endomorphismCodes hn hF hlen
  apply SearchReducible.of_isTotalSearch isTotalSearch_Pigeon ((hn.prod hcode))
    ((snd enc encBits))
  intro a w hw
  change pigeonRel (fun a => n a) (fun p => evalCircuitCode (n p.1) (code p.1) p.2) a w at hw
  obtain ⟨hw, h⟩ := hw
  change w.length = 2 * n a at hw
  have hu : (w.take (n a)).length = n a := by
    simp only [List.length_take]
    omega
  have hv : (w.drop (n a)).length = n a := by
    simp only [List.length_drop]
    omega
  exact ⟨hw, by simpa only [hsem a _ hu, hsem a _ hv] using h⟩

/-- A uniform polynomial-time end-of-line family reduces to its circuit presentation. -/
theorem endOfLineRel_searchReducible_EndOfLine {n : α → ℕ}
    {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc encEndOfLine (endOfLineRel n P S) EndOfLine := by
  obtain ⟨cP, hcP, hPs⟩ := exists_endomorphismCodes hn hP hP_len
  obtain ⟨cS, hcS, hSs⟩ := exists_endomorphismCodes hn hS hS_len
  apply SearchReducible.of_isTotalSearch isTotalSearch_EndOfLine
    ((hn.prod (hcP.prod hcS))) ((snd enc encBits))
  intro a u hw
  let P' (p : α × List Bool) := evalCircuitCode (n p.1) (cP p.1) p.2
  let S' (p : α × List Bool) := evalCircuitCode (n p.1) (cS p.1) p.2
  change endOfLineRel n P' S' a u at hw
  have hu := hw.1
  have hin : hasIn n P' S' a u = hasIn n P S a u := by
    simp only [hasIn, P', S', hPs a u hu, hSs a _ (hP_len a u hu)]
  have hout : hasOut n P' S' a u = hasOut n P S a u := by
    simp only [hasOut, P', S', hSs a u hu, hPs a _ (hS_len a u hu)]
  exact ⟨hu, by simpa only [hin, hout] using hw.2⟩

/-- A uniform polynomial-time undirected parity family reduces to its circuit presentation. -/
theorem leafRel_searchReducible_Leaf {n : α → ℕ} {N₁ N₂ : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hN₂ : ComputableInPolyTime N₂ (encPair enc encBits) encBits)
    (hN₁_len : ∀ a u, u.length = n a → (N₁ (a, u)).length = n a)
    (hN₂_len : ∀ a u, u.length = n a → (N₂ (a, u)).length = n a) :
    SearchReducible enc encLeaf (leafRel n N₁ N₂) Leaf := by
  obtain ⟨c₁, hc₁, h₁⟩ := exists_endomorphismCodes hn hN₁ hN₁_len
  obtain ⟨c₂, hc₂, h₂⟩ := exists_endomorphismCodes hn hN₂ hN₂_len
  apply SearchReducible.of_isTotalSearch isTotalSearch_Leaf
    ((hn.prod (hc₁.prod hc₂))) ((snd enc encBits))
  intro a u hw
  let N₁' (p : α × List Bool) := evalCircuitCode (n p.1) (c₁ p.1) p.2
  let N₂' (p : α × List Bool) := evalCircuitCode (n p.1) (c₂ p.1) p.2
  change leafRel n N₁' N₂' a u at hw
  have hu := hw.1
  have hedge (v : List Bool) (hv : v.length = n a) :
      undirectedEdge N₁' N₂' a u v = undirectedEdge N₁ N₂ a u v := by
    simp only [undirectedEdge, N₁', N₂', h₁ a u hu, h₂ a u hu, h₁ a v hv, h₂ a v hv]
  have hodd : hasOddDegree N₁' N₂' a u = hasOddDegree N₁ N₂ a u := by
    unfold hasOddDegree
    rw [show N₁' (a, u) = N₁ (a, u) from h₁ a u hu,
      show N₂' (a, u) = N₂ (a, u) from h₂ a u hu,
      hedge _ (hN₁_len a u hu), hedge _ (hN₂_len a u hu)]
  exact ⟨hu, by simpa only [hodd] using hw.2⟩

private theorem exists_costCodes {n : α → ℕ} {C : α × List Bool → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hC : ComputableInPolyTime C (encPair enc encBits) encNat) :
    ∃ code : α → CircuitCode, ComputableInPolyTime code enc encCode ∧
      ∀ a u, u.length = n a → binaryValue (evalCircuitOutputs (code a) u) = C (a, u) := by
  obtain ⟨c, d, hbound⟩ := hC.polyBounded_length.exists_le
  let m (a : α) := c * (2 * (enc a).length + n a + 2) ^ d
  have hm : ComputableInPolyTime m enc encUnary :=
    ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const c)
      ((ComputableInPolyTime.unary_pow d).comp
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_add'
            (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
              (ComputableInPolyTime.encoding_length enc))
            hn)
          (ComputableInPolyTime.const 2)))
  have hword : ComputableInPolyTime
      (fun p : α × List Bool => binaryWord (m p.1) (C p)) (encPair enc encBits) encBits := by
    have hbits := (ComputableInPolyTime.of_eq (f := Nat.bits)
      (encIn := encNat) (encOut := encBits) fun _ => rfl).comp hC
    have hwidth := (hm).comp
      (ComputableInPolyTime.fst enc encBits)
    have hpadding := ComputableInPolyTime.unary_sub.comp
      (hwidth.prod (ComputableInPolyTime.length_bits.comp hbits))
    have hplain := ComputableInPolyTime.bitsAppend
      ((ComputableInPolyTime.bitsReplicate false).comp hpadding)
      (ComputableInPolyTime.bitsReverse.comp hbits)
    simpa only [binaryWord, Function.comp_def] using hplain
  have hword_len (a : α) (u : List Bool) (hu : u.length = n a) :
      (binaryWord (m a) (C (a, u))).length = m a := by
    have hb := hbound (a, u)
    simp only [encNat_apply, length_encPair, encBits_apply, hu] at hb
    have hbits : (C (a, u)).bits.length ≤ m a := by
      rw [show 2 * (enc a).length + 1 + n a + 1 =
        2 * (enc a).length + n a + 2 by omega] at hb
      exact hb
    simp only [binaryWord, List.length_append, List.length_replicate, List.length_reverse]
    omega
  obtain ⟨code, hcode, hsem⟩ := exists_uniformCircuitCodes hn hm
    hword hword_len
  refine ⟨code, hcode, fun a u hu => ?_⟩
  rw [hsem a u hu, binaryValue_binaryWord]

/-- A uniform polynomial-time local-search family reduces to the canonical circuit problem.
Costs are encoded with leading zeros, so the comparison is unchanged. -/
theorem localOptRel_searchReducible_LocalOpt {n : α → ℕ}
    {N : α × List Bool → List Bool} {C : α × List Bool → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN : ComputableInPolyTime N (encPair enc encBits) encBits)
    (hC : ComputableInPolyTime C (encPair enc encBits) encNat)
    (hlen : ∀ a u, u.length = n a → (N (a, u)).length = n a) :
    SearchReducible enc encLocalOpt (localOptRel n N C) LocalOpt := by
  obtain ⟨cN, hcN, hNs⟩ := exists_endomorphismCodes hn hN hlen
  obtain ⟨cC, hcC, hCs⟩ := exists_costCodes hn hC
  apply SearchReducible.of_isTotalSearch isTotalSearch_LocalOpt
    ((hn.prod (hcN.prod hcC))) ((snd enc encBits))
  intro a u hw
  change u.length = n a ∧
    binaryValue (evalCircuitOutputs (cC a) u) ≤
      binaryValue (evalCircuitOutputs (cC a) (evalCircuitCode (n a) (cN a) u)) at hw
  refine ⟨hw.1, ?_⟩
  simpa only [hNs a u hw.1, hCs a u hw.1, hCs a _ (hlen a u hw.1)] using hw.2

/-- Circuit `Pigeon` is complete for `PPP` under polynomial-time search reductions. -/
theorem Pigeon_searchComplete : SearchComplete @PPP encPigeon Pigeon := by
  refine ⟨Pigeon_mem_PPP, fun _ enc R hR => ?_⟩
  obtain ⟨-, n, F, hn, hF, hlen, hred⟩ := mem_PPP.mp hR
  exact hred.trans (pigeonRel_searchReducible_Pigeon hn hF hlen)

/-- Circuit `EndOfLine` is complete for `PPAD` under polynomial-time search reductions. -/
theorem EndOfLine_searchComplete : SearchComplete @PPAD encEndOfLine EndOfLine := by
  refine ⟨EndOfLine_mem_PPAD, fun _ enc R hR => ?_⟩
  obtain ⟨-, n, P, S, hn, hP, hS, hP_len, hS_len, hred⟩ := mem_PPAD.mp hR
  exact hred.trans (endOfLineRel_searchReducible_EndOfLine hn hP hS hP_len hS_len)

/-- Circuit `Leaf` is complete for `PPA` under polynomial-time search reductions. -/
theorem Leaf_searchComplete : SearchComplete @PPA encLeaf Leaf := by
  refine ⟨Leaf_mem_PPA, fun _ enc R hR => ?_⟩
  obtain ⟨-, n, N₁, N₂, hn, hN₁, hN₂, hN₁_len, hN₂_len, hred⟩ := mem_PPA.mp hR
  exact hred.trans (leafRel_searchReducible_Leaf hn hN₁ hN₂ hN₁_len hN₂_len)

/-- Circuit `LocalOpt` is complete for `PLS` under polynomial-time search reductions. -/
theorem LocalOpt_searchComplete : SearchComplete @PLS encLocalOpt LocalOpt := by
  refine ⟨LocalOpt_mem_PLS, fun _ enc R hR => ?_⟩
  obtain ⟨-, n, N, C, hn, hN, hC, hlen, hred⟩ := mem_PLS.mp hR
  exact hred.trans (localOptRel_searchReducible_LocalOpt hn hN hC hlen)

end Cslib.Complexity
