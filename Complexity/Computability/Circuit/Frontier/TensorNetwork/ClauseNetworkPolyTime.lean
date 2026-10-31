/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ClauseNetwork
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DirectContraction
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
public import Complexity.Logics.Propositional.CNF.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# The clause network in polynomial time

The clause network of a formula (`Cslib.Circuits.Frontier.ClauseNetwork.clauseNetwork`) is
computable in polynomial time from the encoded formula, with its number of rows in binary and the
network in the encoding of the contraction algorithm (`ExplicitTensorNetwork.encExplicitNetwork`).
It is computed from the literal occurrences (`Cslib.Logic.PL.computableInPolyTime_occurrences`):
every port, previous occurrence and falsifying word is a search or a map over the occurrences, and
every table is a map over the first `2 ^ max k 4` numbers, a constant list.

## Main results

* `Cslib.Circuits.Frontier.ClauseNetwork.computableInPolyTime_clauseNetwork`: the clause network
  is polynomial-time.
-/

public section

namespace Cslib.Circuits.Frontier.ClauseNetwork

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Logic.PL
open Cslib.Complexity (encCNF)

variable {α : Type} {inp : α ↪ List Bool}

/-- The encoding of occurrence lists: unary clause and position indices and a binary literal. -/
local notation "encOs" => encList (encOccurrence encNat)

section Data

variable {os : α → List (Occurrence ℕ)} (hos : ComputableInPolyTime os inp encOs)
include hos

theorem computableInPolyTime_occ {u : α → ℕ} (hu : ComputableInPolyTime u inp encUnary) :
    ComputableInPolyTime (fun a => occ (os a) (u a)) inp (encOccurrence encNat) :=
  listGetDWithInput hos hu _

theorem computableInPolyTime_var {u : α → ℕ} (hu : ComputableInPolyTime u inp encUnary) :
    ComputableInPolyTime (fun a => var (os a) (u a)) inp encNat :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (computableInPolyTime_occ hos hu)))

theorem computableInPolyTime_pol {u : α → ℕ} (hu : ComputableInPolyTime u inp encUnary) :
    ComputableInPolyTime (fun a => pol (os a) (u a)) inp encBool :=
  (snd _ _).comp ((snd _ _).comp ((snd _ _).comp (computableInPolyTime_occ hos hu)))

theorem computableInPolyTime_clauseOf {u : α → ℕ} (hu : ComputableInPolyTime u inp encUnary) :
    ComputableInPolyTime (fun a => clauseOf (os a) (u a)) inp encUnary :=
  (fst _ _).comp (computableInPolyTime_occ hos hu)

theorem computableInPolyTime_prev {u : α → ℕ} (hu : ComputableInPolyTime u inp encUnary) :
    ComputableInPolyTime (fun a => prev (os a) (u a)) inp encUnary := by
  unfold prev
  refine optionGetDWithInput (findWithInput (listReverseWithInput (range.comp hu)) ?_) hu
  exact decide_eq' (computableInPolyTime_var (hos.comp (fst _ _)) (snd _ _))
    (computableInPolyTime_var (hos.comp (fst _ _)) (hu.comp (fst _ _)))

theorem computableInPolyTime_length : ComputableInPolyTime (fun a => (os a).length) inp encUnary :=
  (length_list _).comp hos

/-- The ports of a clause, in unary. -/
theorem computableInPolyTime_clausePorts {i : α → ℕ} (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => clausePorts (os a) (i a)) inp (encList encUnary) := by
  unfold clausePorts
  refine mapWithInput (filterWithInput (range.comp (computableInPolyTime_length hos)) ?_) ?_
  · exact decide_eq' (computableInPolyTime_clauseOf (hos.comp (fst _ _)) (snd _ _))
      (hi.comp (fst _ _))
  · exact unary_mul' (const 3) (snd _ _)

/-- The ports of an equality vertex, in unary. -/
theorem computableInPolyTime_qPorts {w : α → ℕ} (hw : ComputableInPolyTime w inp encUnary) :
    ComputableInPolyTime (fun a => qPorts (os a) (w a)) inp (encList encUnary) := by
  unfold qPorts
  refine listAppend' (cons' (unary_mul' (const 3) hw)
    (cons' (unary_add' (unary_mul' (const 3) hw) (const 1)) (const []))) ?_
  refine mapWithInput (filterWithInput (range.comp (computableInPolyTime_length hos)) ?_) ?_
  · exact decide_eq' (computableInPolyTime_prev (hos.comp (fst _ _)) (snd _ _))
      (hw.comp (fst _ _))
  · exact unary_add' (unary_mul' (const 3) (snd _ _)) (const 2)

end Data

private theorem lsbValue_eq_ofBits : ∀ w : List Bool, BitString.lsbValue w = ofBits w
  | [] => rfl
  | c :: w => by
    rw [BitString.lsbValue, lsbValue_eq_ofBits w]
    simp only [ofBits, List.foldr_cons, Nat.bit_val]
    ring

/-- The falsifying word of a list of unary ports. -/
theorem computableInPolyTime_falsifier {os : α → List (Occurrence ℕ)}
    (hos : ComputableInPolyTime os inp encOs) {ps : α → List ℕ}
    (hps : ComputableInPolyTime ps inp (encList encUnary)) :
    ComputableInPolyTime (fun a => falsifier (os a) (ps a)) inp encNat := by
  have hlist : ComputableInPolyTime (fun a => (ps a).map fun j => !pol (os a) (j / 3)) inp
      (encList encBool) :=
    mapWithInput hps (bool_not.comp (computableInPolyTime_pol (hos.comp (fst _ _))
      (unary_div.comp ((snd _ _).prod (const 3)))))
  have hbits := (bits_encList_polyTime encBool).2.comp hlist
  have hnum := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.bitsToNat).comp hbits
  simpa only [falsifier, lsbValue_eq_ofBits, Function.comp_def] using hnum

/-- A bounded table whose entries are polynomial-time at every fixed position. -/
theorem computableInPolyTime_boundedTable (B : ℕ) {w : α → ℕ} {f : α → ℕ → ℕ}
    (hw : ComputableInPolyTime w inp encUnary)
    (hf : ∀ idx, ComputableInPolyTime (fun a => f a idx) inp encNat) :
    ComputableInPolyTime (fun a => boundedTable B (w a) (f a)) inp (encList encNat) := by
  unfold boundedTable
  exact mapFilterConst _ (fun idx _ => binary_lt' (const idx) (binary_pow' (const 2) hw))
    fun idx _ => hf idx

private theorem binaryPorts {ps : α → List ℕ}
    (hps : ComputableInPolyTime ps inp (encList encUnary)) :
    ComputableInPolyTime ps inp (encList encNat) := by
  simpa only [Function.comp_def, List.map_id'] using (map unary_to_binary).comp hps

/-- **Clause vertices are polynomial-time.** -/
theorem computableInPolyTime_clauseVertex (B : ℕ) {os : α → List (Occurrence ℕ)}
    (hos : ComputableInPolyTime os inp encOs) {i : α → ℕ}
    (hi : ComputableInPolyTime i inp encUnary) :
    ComputableInPolyTime (fun a => clauseVertex (os a) B (i a)) inp
      (encPair (encList encNat) (encList encNat)) := by
  have hps := computableInPolyTime_clausePorts hos hi
  have hz := computableInPolyTime_falsifier hos hps
  unfold clauseVertex
  refine (binaryPorts hps).prod (computableInPolyTime_boundedTable B ((length_list _).comp hps)
    fun idx => ?_)
  unfold clauseEntry
  exact ite_decide (decide_eq' (const idx) hz) (const 0) (const 1)

/-- **Equality vertices are polynomial-time.** -/
theorem computableInPolyTime_qVertex (B : ℕ) {os : α → List (Occurrence ℕ)}
    (hos : ComputableInPolyTime os inp encOs) {w : α → ℕ}
    (hw : ComputableInPolyTime w inp encUnary) :
    ComputableInPolyTime (fun a => qVertex (os a) B (w a)) inp
      (encPair (encList encNat) (encList encNat)) := by
  have hps := computableInPolyTime_qPorts hos hw
  have hlen := (length_list _).comp hps
  unfold qVertex
  refine (binaryPorts hps).prod (computableInPolyTime_boundedTable B hlen fun idx => ?_)
  unfold eqEntry
  exact ite_decide (decide_or (decide_eq' (const (encOut := encNat) idx) (const 0))
    (decide_eq' (const (idx + 1)) (binary_pow' (const 2) hlen))) (const 1) (const 0)

/-- **Link vertices are polynomial-time.** -/
theorem computableInPolyTime_linkVertex {u : α → ℕ} (hu : ComputableInPolyTime u inp encUnary) :
    ComputableInPolyTime (fun a => linkVertex (u a)) inp
      (encPair (encList encNat) (encList encNat)) := by
  unfold linkVertex
  refine (binaryPorts (cons' (unary_add' (unary_mul' (const 3) hu) (const 1))
    (cons' (unary_add' (unary_mul' (const 3) hu) (const 2)) (const [])))).prod (const _)

/-- **The network of an occurrence list is polynomial-time**, with its number of rows in binary. -/
theorem computableInPolyTime_network (B : ℕ) {os : α → List (Occurrence ℕ)}
    (hos : ComputableInPolyTime os inp encOs) {m : α → ℕ}
    (hm : ComputableInPolyTime m inp encUnary) :
    ComputableInPolyTime (fun a => network (os a) B (m a)) inp
      (encPair encNat ExplicitTensorNetwork.encExplicitNetwork) := by
  have hN := computableInPolyTime_length hos
  have hout : ComputableInPolyTime (DescribedNetwork.equivProd (T := List ℕ)).symm
      (encPair encUnary (encList (encPair (encList encNat) (encList encNat))))
      ExplicitTensorNetwork.encExplicitNetwork :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hverts : ComputableInPolyTime (fun a =>
      (List.range (m a)).map (clauseVertex (os a) B) ++ (List.range (os a).length).map linkVertex ++
        (List.range (os a).length).map (qVertex (os a) B)) inp
      (encList (encPair (encList encNat) (encList encNat))) :=
    listAppend' (listAppend'
      (mapWithInput (range.comp hm) (computableInPolyTime_clauseVertex B (hos.comp (fst _ _))
        (snd _ _)))
      (mapWithInput (range.comp hN) (computableInPolyTime_linkVertex (snd _ _))))
      (mapWithInput (range.comp hN) (computableInPolyTime_qVertex B (hos.comp (fst _ _))
        (snd _ _)))
  unfold network
  exact (unary_to_binary.comp (unary_add' hm hN)).prod
    (hout.comp ((unary_mul' (const 3) hN).prod hverts))

/-- **The clause network is polynomial-time** from the encoded formula, with its number of rows in
binary. -/
theorem computableInPolyTime_clauseNetwork (k : ℕ) :
    ComputableInPolyTime (clauseNetwork k) encCNF
      (encPair encNat ExplicitTensorNetwork.encExplicitNetwork) :=
  computableInPolyTime_network (max k 4) Complexity.SAT.computableInPolyTime_occurrences
    (Complexity.SAT.computableInPolyTime_length (ComputableInPolyTime.id' (encIn := encCNF)))

end Cslib.Circuits.Frontier.ClauseNetwork
