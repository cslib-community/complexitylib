/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Verifier
public import Complexity.Logics.FirstOrder.Encoding.Sum
public import Complexity.Logics.SecondOrder.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Materializing existential relation witnesses

The certificate layout of an existential second-order sentence already reads a polynomial-length
word as a family of relation tables. This module materializes those tables and appends them to
the original encoded structure. The transformation has a native polynomial-time certificate and
its decoded structure is exactly the expansion by the guessed relations. Missing witness bits
read as false; nullary relations have one table entry, and an empty family adds no tables.

## Main definitions

* `Cslib.Logic.ESO.Sentence.Layout.witnessInput`: append the certificate's relation tables.

## Main results

* `Cslib.Logic.ESO.Sentence.Layout.wellFormed_witnessInput_iff`: materialization preserves and
  reflects the validity of the original input tables.
* `Cslib.Logic.ESO.Sentence.Layout.decode_witnessInput`: the decoded output is the expansion by
  the certificate relations.
* `Cslib.Logic.ESO.Sentence.Layout.computableInPolyTime_witnessInput`: materialization is
  polynomial-time in the original input and certificate lengths.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

public section

universe u v u' v'

open FirstOrder Language Structure Turing.MultiTapeTM

namespace Cslib.Logic.ESO


namespace Sentence.Layout

variable {L : Language.{u, v}} {Φ : Sentence L} (ℓ : Layout Φ) {m : ℕ}
    (e : Fin m ≃ Φ.Var)

/-- A relation table materialized from the certificate, in tuple-index order. -/
@[expose]
def witnessTable (a : EncodedStructure) (w : List Bool) (i : Φ.Var) : List Bool :=
  (List.range (a.1 ^ Φ.arity i)).map fun idx =>
    w.getD (ℓ.position (encStructure a).length i idx) false

/-- Append the materialized witness relations to the original relation tables. The sentence and
its enumeration are fixed parameters, not parts of the machine input. -/
@[expose]
def witnessInput (p : EncodedStructure × List Bool) : EncodedStructure :=
  (p.1.1, p.1.2 ++ List.ofFn fun j : Fin m => ℓ.witnessTable p.1 p.2 (e j))

/-- Materialization does not change the universe. -/
@[simp]
theorem witnessInput_card (p : EncodedStructure × List Bool) :
    (ℓ.witnessInput e p).1 = p.1.1 :=
  rfl

/-- A materialized relation table has one entry for each tuple, including one for arity zero. -/
@[simp]
theorem length_witnessTable (a : EncodedStructure) (w : List Bool) (i : Φ.Var) :
    (ℓ.witnessTable a w i).length = a.1 ^ Φ.arity i := by
  simp [witnessTable]

/-- Reading a materialized table returns the corresponding certificate bit. -/
theorem getD_witnessTable (a : EncodedStructure) (w : List Bool) (i : Φ.Var)
    (x : Fin (Φ.arity i) → Fin a.1) :
    (ℓ.witnessTable a w i).getD (tupleIndex x) false =
      w.getD (ℓ.position (encStructure a).length i (tupleIndex x)) false := by
  rw [List.getD_eq_getElem _ _ (by rw [length_witnessTable]; exact tupleIndex_lt x)]
  simp [witnessTable]

/-- The materialized witness tables always have the declared shapes, even for short certificates.
Short certificates supply false bits to the missing positions. -/
theorem wellFormed_witnessTables (a : EncodedStructure) (w : List Bool) :
    (varLanguage.vocabulary Φ.arity e).WellFormed
      (a.1, List.ofFn fun j : Fin m => ℓ.witnessTable a w (e j)) := by
  constructor
  · exact List.length_ofFn
  · intro j
    change Fin m at j
    change ((List.ofFn fun j : Fin m => ℓ.witnessTable a w (e j)).getD j []).length =
      a.1 ^ Φ.arity (e j)
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp only [List.getElem_ofFn, length_witnessTable]

variable {K : Language.{u', v'}} (v : Vocabulary K)

/-- Appending witness tables preserves and reflects source shape validity; it cannot repair a
missing, extra, or incorrectly sized source relation table. -/
theorem wellFormed_witnessInput_iff (a : EncodedStructure) (w : List Bool) :
    (v.sum (varLanguage.vocabulary Φ.arity e)).WellFormed (ℓ.witnessInput e (a, w)) ↔
      v.WellFormed a := by
  change (v.sum (varLanguage.vocabulary Φ.arity e)).WellFormed
    (a.1, a.2 ++ List.ofFn fun j : Fin m => ℓ.witnessTable a w (e j)) ↔ v.WellFormed a
  exact (Vocabulary.wellFormed_sum_iff v (varLanguage.vocabulary Φ.arity e)
    a.1 a.2 _ List.length_ofFn).trans (and_iff_left (ℓ.wellFormed_witnessTables e a w))

/-- The output decodes to exactly the input structure expanded by the certificate relations. -/
theorem decode_witnessInput [K.IsRelational] (a : EncodedStructure) (w : List Bool)
    (ha : v.WellFormed a) :
    (v.sum (varLanguage.vocabulary Φ.arity e)).decode (ℓ.witnessInput e (a, w)) =
      @sumStructure K (varLanguage Φ.arity) (Fin a.1) (v.decode a)
        (varLanguage.structure (ℓ.certRel a.1 (encStructure a).length w)) := by
  apply FirstOrder.Language.Structure.ext
  · funext k f
    exact isEmptyElim f
  · funext k r x
    change Fin k → Fin a.1 at x
    apply propext
    cases r with
    | inl r =>
      change ((v.sum (varLanguage.vocabulary Φ.arity e)).table
        (a.1, a.2 ++ List.ofFn fun j : Fin m => ℓ.witnessTable a w (e j))
        ⟨k, Sum.inl r⟩).getD (tupleIndex x) false = true ↔ _
      erw [Vocabulary.table_sum_inl v (varLanguage.vocabulary Φ.arity e)
        a.1 a.2 _ ha.1 ⟨k, r⟩]
      rfl
    | inr r =>
      obtain ⟨i, rfl⟩ := r
      change ((v.sum (varLanguage.vocabulary Φ.arity e)).table
        (a.1, a.2 ++ List.ofFn fun j : Fin m => ℓ.witnessTable a w (e j))
        ⟨Φ.arity i, Sum.inr ⟨i, rfl⟩⟩).getD (tupleIndex x) false = true ↔ _
      erw [Vocabulary.table_sum_inr v (varLanguage.vocabulary Φ.arity e)
        a.1 a.2 _ ha.1 ⟨Φ.arity i, ⟨i, rfl⟩⟩]
      change ((List.ofFn fun j : Fin m => ℓ.witnessTable a w (e j)).getD
        (e.symm i : ℕ) []).getD (tupleIndex x) false = true ↔ _
      rw [List.getD_eq_getElem
        (List.ofFn fun j : Fin m => ℓ.witnessTable a w (e j)) []
        (by simp)]
      simp only [List.getElem_ofFn]
      change (ℓ.witnessTable a w (e (e.symm i))).getD (tupleIndex x) false = true ↔
        x ∈ ℓ.certRel a.1 (encStructure a).length w i
      rw [Equiv.apply_symm_apply]
      erw [getD_witnessTable ℓ a w i x]
      rfl

/-- The exact additional encoding cost is the sum of the framed witness-table lengths. -/
theorem length_encStructure_witnessInput (a : EncodedStructure) (w : List Bool) :
    (encStructure (ℓ.witnessInput e (a, w))).length = (encStructure a).length +
      ∑ j : Fin m, (2 * a.1 ^ Φ.arity (e j) + 1) := by
  simp [witnessInput, encStructure, length_encList, List.sum_ofFn, Nat.add_assoc]

/-- A uniform polynomial bound in the original encoded input length, independent of witness
contents and length. The sentence and layout determine the constants and degree. -/
theorem length_encStructure_witnessInput_le (a : EncodedStructure) (w : List Bool) :
    (encStructure (ℓ.witnessInput e (a, w))).length ≤ (encStructure a).length +
      m * (2 * (encStructure a).length ^ ℓ.degree + 1) := by
  have hN : 0 < (encStructure a).length := by
    simp only [encStructure, length_encPair]
    omega
  have hp (j : Fin m) : a.1 ^ Φ.arity (e j) ≤ (encStructure a).length ^ ℓ.degree :=
    (Nat.pow_le_pow_left (card_le_length_encStructure a) _).trans
      (Nat.pow_le_pow_right hN (ℓ.arity_le (e j)))
  rw [length_encStructure_witnessInput]
  exact Nat.add_le_add_left
    ((Finset.sum_le_sum fun j _ => Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hp j)) 1).trans_eq
      (by simp)) _

open ComputableInPolyTime

/-- Materializing one fixed relation uses polynomially many certificate lookups. -/
@[fun_prop]
theorem computableInPolyTime_witnessTable (i : Φ.Var) :
    ComputableInPolyTime (fun p : EncodedStructure × List Bool => ℓ.witnessTable p.1 p.2 i)
      (encPair encStructure encBits) encBits := by
  unfold witnessTable
  refine mapToBitsWithInput (range.comp ((unary_pow _).comp
    ((fst encUnary (encList encBits)).comp (fst encStructure encBits)))) ?_
  refine bitsGetDWithInput
    ((snd encStructure encBits).comp (fst (encPair encStructure encBits) encUnary)) ?_ false
  unfold position
  exact unary_add' (unary_mul' (const (ℓ.block i : ℕ))
    ((unary_pow ℓ.degree).comp ((encoding_length encStructure).comp
      ((fst encStructure encBits).comp (fst (encPair encStructure encBits) encUnary)))))
    (snd (encPair encStructure encBits) encUnary)

/-- The entire witness expansion is computed by an actual polynomial-time machine on the input
and certificate. No well-formedness or certificate-length premise is needed for its running time. -/
@[fun_prop]
theorem computableInPolyTime_witnessInput :
    ComputableInPolyTime (ℓ.witnessInput e) (encPair encStructure encBits) encStructure := by
  unfold witnessInput
  refine ((fst encUnary (encList encBits)).comp (fst encStructure encBits)).prod
    (listAppend' ((snd encUnary (encList encBits)).comp (fst encStructure encBits)) ?_)
  simpa only [List.ofFn_eq_map] using
    mapConst (List.finRange m) (fun j _ => ℓ.computableInPolyTime_witnessTable (e j))

end Sentence.Layout

end Cslib.Logic.ESO
