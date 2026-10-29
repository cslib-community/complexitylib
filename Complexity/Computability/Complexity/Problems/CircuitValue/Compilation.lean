/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CircuitValue.Completeness
public import Complexity.Computability.Circuit.Boolean.CodeSubstitution
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Uniform circuit compilation for polynomial-time function families

The Boolean tableau compiler is applied to a fixed output-bit selector. Hardwiring its instance
and selector inputs, and combining its outputs, gives circuit codes for fixed-length function
families. Construction time is certified separately from circuit semantics.

The selector has a fixed length equal to the output width. All output-bit circuits therefore
have equal gate counts and can be bundled by fixed offsets. The construction repeats the
computation for each output; it establishes polynomial construction time without an optimized
gate count. Arbitrary instance encodings need no decoder, and correctness concerns their image.

## Main results

* `Cslib.Complexity.CircuitValue.exists_uniformCircuitFamily`: one polynomial-time circuit-code
  constructor for an entire polynomial-time family, with separately prescribed unary widths.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.CircuitValue

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

private def selector (width index : ℕ) : List Bool :=
  List.replicate index true ++ List.replicate (width - index) false

private theorem length_selector {width index : ℕ} (h : index ≤ width) :
    (selector width index).length = width := by
  simp only [selector, List.length_append, List.length_replicate]
  omega

private theorem count_selector (width index : ℕ) : (selector width index).count true = index := by
  have hz : (List.replicate (width - index) false).count true = 0 := by
    apply List.count_eq_zero.mpr
    simp
  simp [selector, hz]

private def bitPrefix {α : Type} (enc : α ↪ List Bool) (m : α → ℕ) (a : α) (j : ℕ) :
    List Bool := frame (enc a) ++ frame (selector (m a) j)

private theorem length_bitPrefix {α : Type} (enc : α ↪ List Bool) (m : α → ℕ)
    (a : α) {j : ℕ} (hj : j ≤ m a) :
    (bitPrefix enc m a j).length = 2 * (enc a).length + 2 * m a + 2 := by
  simp only [bitPrefix, List.length_append, length_frame, length_selector hj]
  omega

private theorem polytime_bitPrefix {α : Type} {enc : α ↪ List Bool} {m : α → ℕ}
    (hm : ComputableInPolyTime m enc encUnary) :
    ComputableInPolyTime (fun p : α × ℕ => bitPrefix enc m p.1 p.2)
      (encPair enc encUnary) encBits := by
  have hframe : ComputableInPolyTime Turing.MultiTapeTM.frame encBits encBits :=
    ComputableInPolyTime.frame
  unfold bitPrefix selector
  fun_prop

private theorem polytime_outputBit {α : Type} {enc : α ↪ List Bool}
    {F : α × List Bool → List Bool}
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits) :
    ComputableInPolyTime
      (fun p : α × (List Bool × List Bool) => (F (p.1, p.2.2)).getD (p.2.1.count true) false)
      (encPair enc (encPair encBits encBits)) encBool := by
  fun_prop

private theorem exists_uniformOutputBits {α : Type} {enc : α ↪ List Bool}
    {n m : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits) :
    ∃ cs : (a : α) → ℕ → Circuit signature (n a) 1,
      ComputableInPolyTime (fun p : α × ℕ => (cs p.1 p.2).code)
        (encPair enc encUnary) encCode ∧
      (∀ a j, j ≤ m a → (cs a j).size = (cs a 0).size) ∧
      ∀ a j (x : Fin (n a) → Bool),
        (cs a j).eval interpretation x 0 = (F (a, List.ofFn x)).getD j false := by
  obtain ⟨circuits, hcode, hcorrect⟩ := exists_uniformCircuits (polytime_outputBit hF)
  let cs (a : α) (j : ℕ) : Circuit signature (n a) 1 :=
    prefixCircuit (bitPrefix enc m a j)
      (circuits ((bitPrefix enc m a j).length + n a))
  have hprefix := polytime_bitPrefix hm
  have hlength : ComputableInPolyTime
      (fun p : α × ℕ => (bitPrefix enc m p.1 p.2).length + n p.1)
      (encPair enc encUnary) encUnary := by
    fun_prop
  refine ⟨cs, ?_, ?_, ?_⟩
  · have h := computableInPolyTime_prefixCode hprefix
      (ComputableInPolyTime.unary_to_binary.comp (hn.comp (ComputableInPolyTime.fst enc encUnary)))
      (hcode.comp hlength)
    exact h.of_enc_eq fun p => by
      rw [show (cs p.1 p.2).code = _ from code_prefixCircuit _ _]
      rfl
  · intro a j hj
    simp only [cs, size_prefixCircuit]
    rw [length_bitPrefix enc m a hj, length_bitPrefix enc m a (Nat.zero_le _)]
  · intro a j x
    have hcorrectOfFn (p : α × (List Bool × List Bool)) (N : ℕ) (y : Fin N → Bool)
        (hy : encPair enc (encPair encBits encBits) p = List.ofFn y) :
        (circuits N).eval interpretation y 0 =
          (F (p.1, p.2.2)).getD (p.2.1.count true) false := by
      have hN := congrArg List.length hy
      simp only [List.length_ofFn] at hN
      subst N
      have hw : (fun i : Fin (encPair enc (encPair encBits encBits) p).length =>
          (encPair enc (encPair encBits encBits) p)[i]) = y :=
        List.ofFn_injective (List.ofFn_getElem.trans hy)
      simpa only [hw] using hcorrect p
    let r := bitPrefix enc m a j
    let u := List.ofFn x
    have hin : encPair enc (encPair encBits encBits) (a, (selector (m a) j, u)) = r ++ u := by
      simp [encPair_apply, encBits_apply, r, bitPrefix, List.append_assoc]
    have hw : List.ofFn (Fin.append (fun i : Fin r.length => r[i.val]) x) = r ++ u := by
      rw [List.ofFn_fin_append, List.ofFn_getElem]
    change (prefixCircuit r (circuits (r.length + n a))).eval interpretation x 0 = _
    rw [eval_prefixCircuit]
    simpa only [count_selector, u] using
      hcorrectOfFn (a, (selector (m a) j, u)) _ _ (hin.trans hw.symm)

/-- Compile a polynomial-time function family into circuits with prescribed input and output
widths. One polynomial-time constructor outputs the code for every instance. Output `j` is the
`j`th bit of the function value, defaulting to `false` when that value is shorter than `m a`. -/
theorem exists_uniformCircuitFamily {α : Type} {enc : α ↪ List Bool}
    {n m : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits) :
    ∃ circuits : (a : α) → Circuit signature (n a) (m a),
      ComputableInPolyTime (fun a => (circuits a).code) enc encCode ∧
      ∀ a (x : Fin (n a) → Bool) (j : Fin (m a)),
        (circuits a).eval interpretation x j = (F (a, List.ofFn x)).getD j.val false := by
  obtain ⟨bits, hbits, hsize, hsem⟩ := exists_uniformOutputBits hn hm hF
  let circuits (a : α) : Circuit signature (n a) (m a) :=
    Circuit.pi (fun j : Fin (m a) => bits a j.val)
  have hzero := hbits.comp ((ComputableInPolyTime.id' (encIn := enc)).prod
    (ComputableInPolyTime.const 0))
  have hblock : ComputableInPolyTime (fun a => (bits a 0).size) enc encNat := by
    have h := (ComputableInPolyTime.length_list_binary encGate).comp hzero.fst'
    convert h using 1
    funext a
    exact (Circuit.length_code_fst (bits a 0)).symm
  have hlist : ComputableInPolyTime
      (fun a => (List.range (m a)).map (fun j => (bits a j).code)) enc (encList encCode) :=
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hm) hbits
  have hlistEq (a : α) : (List.range (m a)).map (fun j => (bits a j).code) =
      List.ofFn (fun j : Fin (m a) => (bits a j.val).code) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp
  have hcompiled := computableInPolyTime_bundleCode
    (ComputableInPolyTime.unary_to_binary.comp hn) hblock hlist
  refine ⟨circuits, hcompiled.of_enc_eq (fun a => ?_), fun a x j => ?_⟩
  · change encCode (circuits a).code = encCode
      (bundleCode (n a) (bits a 0).size ((List.range (m a)).map (fun j => (bits a j).code)))
    rw [hlistEq, bundleCode_code _ _ (fun j => hsize a j.val j.isLt.le)]
  · exact (congrFun (Circuit.eval_pi _ x) j).trans (hsem a j.val x)

end Cslib.Complexity.CircuitValue
