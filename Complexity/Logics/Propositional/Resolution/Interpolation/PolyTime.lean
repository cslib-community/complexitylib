/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Interpolation.Extraction
public import Complexity.Logics.Propositional.Resolution.Interpolation.MonotoneExtraction
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Complexity.Logics.Propositional.CNF.PolyTime

/-!
# Extracting interpolants in polynomial time

The extraction of interpolant circuits from resolution refutations
(`Cslib.Logic.PL.CNF.interpolantCode`) runs in polynomial time
(`Cslib.Logic.PL.CNF.computableInPolyTime_interpolantCode`). Its input is the number `n` of
inputs of the circuit in unary, as in `Cslib.Circuits.Boolean.encCircuit`, then the two formulas
and the lines; a variable is a shared variable in binary or a private variable in any encoding with
decidable equality, and clauses and formulas are encoded as lists, as in
`Complexity.Logics.Propositional.CNF.PolyTime`. Its output is the code of the circuit in the
binary encoding `Cslib.Circuits.Boolean.encCode`.

Together with `Cslib.Logic.PL.CNF.IsProof.ofCode_interpolantCode`, this is the effective form of
feasible interpolation [Krajíček, Theorem 6.1][Krajicek1997], [Pudlák, Theorem 1][Pudlak1997]:
the interpolant circuit of a refutation is computed from its lines in polynomial time. The bound is
not explicit; each line is justified by scanning all pairs of earlier lines and all literals of the
first, so the running time is polynomial in the number of lines and their widths.

The same holds for the monotone interpolant (`Cslib.Logic.PL.CNF.monotoneInterpolantCode`), from
the same input, with its output in the binary encoding of monotone circuits
`Cslib.Circuits.Monotone.encCode`
(`Cslib.Logic.PL.CNF.computableInPolyTime_monotoneInterpolantCode`).
Together with `Cslib.Logic.PL.CNF.IsProof.ofCode_monotoneInterpolantCode`, this is the effective
form of monotone feasible interpolation [Pudlák, Theorem 2][Pudlak1997].

## Main results

* `Cslib.Logic.PL.CNF.computableInPolyTime_interpolantCode`: the extraction runs in polynomial
  time.
* `Cslib.Logic.PL.CNF.computableInPolyTime_monotoneInterpolantCode`: so does the extraction of the
  monotone interpolant.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
* [P. Pudlák, *Lower bounds for resolution and cutting plane proofs and monotone
  computations*][Pudlak1997]
-/

public section

namespace Cslib.Logic.PL

open Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

variable {Y Z : Type}

namespace Interpolant

variable {encY : Y ↪ List Bool} {encZ : Z ↪ List Bool}

/-! ### Variables -/

/-- Embedding the `A`-variables into the joint variables, by option elimination. -/
private theorem sumMap_inl_eq (v : ℕ ⊕ Y) :
    (Sum.map id Sum.inl v : ℕ ⊕ (Y ⊕ Z)) =
      v.getLeft?.elim (v.getRight?.elim (.inl 0) fun y => .inr (.inl y)) fun i => .inl i := by
  rcases v with _ | _ <;> rfl

/-- Embedding the `B`-variables into the joint variables, by option elimination. -/
private theorem sumMap_inr_eq (v : ℕ ⊕ Z) :
    (Sum.map id Sum.inr v : ℕ ⊕ (Y ⊕ Z)) =
      v.getLeft?.elim (v.getRight?.elim (.inl 0) fun z => .inr (.inr z)) fun i => .inl i := by
  rcases v with _ | _ <;> rfl

private theorem getLeft? {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (Sum.getLeft? (α := α) (β := β)) (encSum encA encB) (encOption encA) :=
  (ComputableInO.getLeft?_deg encA encB).computableInPolyTime

private theorem getRight? {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (Sum.getRight? (α := α) (β := β)) (encSum encA encB) (encOption encB) :=
  (ComputableInO.getRight?_deg encA encB).computableInPolyTime

private theorem isLeft {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (Sum.isLeft (α := α) (β := β)) (encSum encA encB) encBool :=
  (ComputableInO.isLeft_deg encA encB).computableInPolyTime

/-- The embedding of the `A`-variables is polynomial-time. -/
private theorem sumMap_inl :
    ComputableInPolyTime (Sum.map id Sum.inl : ℕ ⊕ Y → ℕ ⊕ (Y ⊕ Z)) (encSum encNat encY)
      (encSum encNat (encSum encY encZ)) := by
  simp only [funext sumMap_inl_eq]
  exact optionElimWithInput (getLeft? _ _)
    (optionElimWithInput (getRight? _ _) (const _)
      ((sumInr _ _).comp ((sumInl _ _).comp (snd _ _))))
    ((sumInl _ _).comp (snd _ _))

/-- The embedding of the `B`-variables is polynomial-time. -/
private theorem sumMap_inr :
    ComputableInPolyTime (Sum.map id Sum.inr : ℕ ⊕ Z → ℕ ⊕ (Y ⊕ Z)) (encSum encNat encZ)
      (encSum encNat (encSum encY encZ)) := by
  simp only [funext sumMap_inr_eq]
  exact optionElimWithInput (getLeft? _ _)
    (optionElimWithInput (getRight? _ _) (const _)
      ((sumInr _ _).comp ((sumInr _ _).comp (snd _ _))))
    ((sumInl _ _).comp (snd _ _))

/-! ### Gates -/

/-- The gates of a resolution step, by option elimination on the variable. -/
private theorem resolventGates_eq (base w₁ w₂ : ℕ) (v : ℕ ⊕ (Y ⊕ Z)) :
    resolventGates base w₁ w₂ v =
      v.getLeft?.elim
        (if v.getRight?.elim false Sum.isLeft then padGate (.or, [w₁, w₂])
          else padGate (.and, [w₁, w₂]))
        fun i =>
          [(.not, [i]), (.and, [base, w₁]), (.and, [i, w₂]), (.or, [base + 1, base + 2])] := by
  rcases v with _ | _ | _ <;> rfl

/-- A gate list with three constant gates before a binary gate on computed wires. -/
private theorem padGate_binary {γ : Type} {encIn : γ ↪ List Bool} (op : Op) {w₁ w₂ : γ → ℕ}
    (h₁ : ComputableInPolyTime w₁ encIn encNat) (h₂ : ComputableInPolyTime w₂ encIn encNat) :
    ComputableInPolyTime (fun x => padGate (op, [w₁ x, w₂ x])) encIn (encList encGate) := by
  unfold padGate
  exact cons' (const _) (cons' (const _) (cons' (const _)
    (cons' ((const op).prod (cons' h₁ (cons' h₂ (const [])))) (const []))))

/-- The gates of a resolution step are computed in polynomial time from the wires, in binary,
and the variable. -/
private theorem resolventGates_polyTime :
    ComputableInPolyTime (fun r : (ℕ × ℕ × ℕ) × (ℕ ⊕ (Y ⊕ Z)) =>
        resolventGates r.1.1 r.1.2.1 r.1.2.2 r.2)
      (encPair (encPair encNat (encPair encNat encNat)) (encSum encNat (encSum encY encZ)))
      (encList encGate) := by
  simp only [resolventGates_eq]
  have hr := id' (encIn := encPair (encPair encNat (encPair encNat encNat))
    (encSum encNat (encSum encY encZ)))
  have hv := hr.snd'
  have hbase := hr.fst'.fst'
  have hw₁ := hr.fst'.snd'.fst'
  have hw₂ := hr.fst'.snd'.snd'
  have hadd := (ComputableTidilyInPolyTime.binary_add).computableInPolyTime
  refine optionElimWithInput ((getLeft? _ _).comp hv)
    (ite (optionElimWithInput ((getRight? _ _).comp hv) (const false)
      ((isLeft _ _).comp (snd _ _))) (padGate_binary _ hw₁ hw₂) (padGate_binary _ hw₁ hw₂)) ?_
  have hq := fst (encPair (encPair encNat (encPair encNat encNat))
    (encSum encNat (encSum encY encZ))) encNat
  have hi := snd (encPair (encPair encNat (encPair encNat encNat))
    (encSum encNat (encSum encY encZ))) encNat
  have hb := hq.fst'.fst'
  exact cons' ((const _).prod (cons' hi (const [])))
    (cons' ((const _).prod (cons' hb (cons' hq.fst'.snd'.fst' (const []))))
      (cons' ((const _).prod (cons' hi (cons' hq.fst'.snd'.snd' (const []))))
        (cons' ((const _).prod (cons' (hadd.comp (hb.prod (const 1)))
          (cons' (hadd.comp (hb.prod (const 2))) (const [])))) (const []))))

variable [DecidableEq Y] [DecidableEq Z]

/-- Resolvents are computed in polynomial time. -/
private theorem resolvent_polyTime :
    ComputableInPolyTime (fun q : (Clause (ℕ ⊕ (Y ⊕ Z)) × Clause (ℕ ⊕ (Y ⊕ Z))) × (ℕ ⊕ (Y ⊕ Z)) =>
        q.1.1.resolvent q.1.2 q.2)
      (encPair (encPair (encList (encPair (encSum encNat (encSum encY encZ)) encBool))
        (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))
        (encSum encNat (encSum encY encZ)))
      (encList (encPair (encSum encNat (encSum encY encZ)) encBool)) := by
  unfold Clause.resolvent
  have hq := id' (encIn := encPair (encPair (encList (encPair (encSum encNat (encSum encY encZ))
    encBool)) (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))
    (encSum encNat (encSum encY encZ)))
  exact listAppend' (filterWithInput hq.fst'.fst'
      (decide_not (decide_eq' (snd _ _) ((fst _ _).snd'.prod (const true)))))
    (filterWithInput hq.fst'.snd'
      (decide_not (decide_eq' (snd _ _) ((fst _ _).snd'.prod (const false)))))

/-- Candidate resolution steps are listed in polynomial time. -/
private theorem candidates_polyTime {V : Type} {encV : V ↪ List Bool} :
    ComputableInPolyTime (candidates (V := V)) (encList (encList (encPair encV encBool)))
      (encList (encPair (encPair (encList (encPair encV encBool)) encUnary)
        (encPair (encPair (encList (encPair encV encBool)) encUnary) encV))) := by
  have hzip :=
    (ComputableTidilyInPolyTime.zipIdx (encList (encPair encV encBool))).computableInPolyTime
  unfold candidates
  refine flatMapWithInput hzip (flatMapWithInput (hzip.comp (fst _ _))
    (mapWithInput (fst _ _).snd'.fst' ?_))
  exact (fst _ _).fst'.snd'.prod ((fst _ _).snd'.prod (snd _ _).fst')

/-- The four gates of a line are computed in polynomial time from the number of inputs in unary,
the two formulas, the earlier lines and the line. -/
private theorem lineGates_polyTime :
    ComputableInPolyTime (fun q : (ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z))) ×
        (List (Clause (ℕ ⊕ (Y ⊕ Z))) × Clause (ℕ ⊕ (Y ⊕ Z))) =>
          lineGates q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2)
      (encPair (encPair encUnary (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
          (encList (encList (encPair (encSum encNat encZ) encBool)))))
        (encPair (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))
          (encList (encPair (encSum encNat (encSum encY encZ)) encBool))))
      (encList encGate) := by
  have hq := id' (encIn := encPair (encPair encUnary
    (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
      (encList (encList (encPair (encSum encNat encZ) encBool)))))
    (encPair (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))
      (encList (encPair (encSum encNat (encSum encY encZ)) encBool))))
  have hn := hq.fst'.fst'
  have hc := hq.snd'.snd'
  have hE := hq.snd'.fst'
  have hmemA := decide_mem ((CNF.computableInPolyTime_relabel (sumMap_inl (encZ := encZ))).comp
    hq.fst'.snd'.fst') hc
  have hmemB := decide_mem ((CNF.computableInPolyTime_relabel (sumMap_inr (encY := encY))).comp
    hq.fst'.snd'.snd') hc
  have hbin := ComputableTidilyInPolyTime.unary_to_binary.computableInPolyTime
  -- the search for a resolution step deriving the line
  have hp := id' (encIn := encPair (encPair (encPair encUnary
    (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
      (encList (encList (encPair (encSum encNat encZ) encBool)))))
    (encPair (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))
      (encList (encPair (encSum encNat (encSum encY encZ)) encBool))))
    (encPair (encPair (encList (encPair (encSum encNat (encSum encY encZ)) encBool)) encUnary)
      (encPair (encPair (encList (encPair (encSum encNat (encSum encY encZ)) encBool)) encUnary)
        (encSum encNat (encSum encY encZ)))))
  have hc₁ := hp.snd'.fst'.fst'
  have hc₂ := hp.snd'.snd'.fst'.fst'
  have hv := hp.snd'.snd'.snd'
  have htest := decide_and (decide_mem hc₁ (hv.prod (const true)))
    (decide_and (decide_mem hc₂ (hv.prod (const false)))
      (decide_eq' (resolvent_polyTime.comp ((hc₁.prod hc₂).prod hv)) hp.fst'.snd'.snd'))
  have hfind := findWithInput (test := fun q t => decide ((t.2.2, true) ∈ t.1.1 ∧
    (t.2.2, false) ∈ t.2.1.1 ∧ t.1.1.resolvent t.2.1.1 t.2.2 = q.2.2))
    (candidates_polyTime.comp hE) htest
  -- the gates of the step found
  have hm := hp.fst'.fst'.fst'
  have hbody := resolventGates_polyTime.comp
      (((hbin.comp (unary_add' hm (unary_mul' (const 4)
        ((length_list _).comp hp.fst'.snd'.fst')))).prod
      ((hbin.comp (unary_add' (unary_add' hm (unary_mul' (const 4) hp.snd'.fst'.snd'))
        (const 3))).prod
      (hbin.comp (unary_add' (unary_add' hm (unary_mul' (const 4) hp.snd'.snd'.fst'.snd'))
        (const 3))))).prod hv)
  unfold lineGates
  exact ite_decide hmemA (const _) (ite_decide hmemB (const _)
    (optionElimWithInput (body := fun (q : (ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z))) ×
        (List (Clause (ℕ ⊕ (Y ⊕ Z))) × Clause (ℕ ⊕ (Y ⊕ Z))))
        (t : (Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) × (Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) × (ℕ ⊕ (Y ⊕ Z))) =>
      resolventGates (q.1.1 + 4 * q.2.1.length) (q.1.1 + 4 * t.1.2 + 3)
        (q.1.1 + 4 * t.2.1.2 + 3) t.2.2) hfind (const _) hbody))

end Interpolant

variable [DecidableEq Y] [DecidableEq Z]

/-- **Extracting interpolants in polynomial time.** The code of the interpolant circuit of a
resolution refutation (`Cslib.Logic.PL.CNF.interpolantCode`) is computed in polynomial time from
the number of inputs in unary, the two formulas and the lines of the refutation. Shared variables
are written in binary, private variables in any encodings `encY` and `encZ`, and the circuit code
in the binary encoding `Cslib.Circuits.Boolean.encCode`. On a refutation, the code is that of a
circuit computing an interpolant (`Cslib.Logic.PL.CNF.IsProof.ofCode_interpolantCode`). -/
theorem CNF.computableInPolyTime_interpolantCode (encY : Y ↪ List Bool) (encZ : Z ↪ List Bool) :
    ComputableInPolyTime (fun p : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
        List (Clause (ℕ ⊕ (Y ⊕ Z))) => CNF.interpolantCode p.1 p.2.1.1 p.2.1.2 p.2.2)
      (encPair encUnary (encPair (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
        (encList (encList (encPair (encSum encNat encZ) encBool))))
        (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))))
      encCode := by
  have hp := id' (encIn := encPair encUnary (encPair (encPair
    (encList (encList (encPair (encSum encNat encY) encBool)))
    (encList (encList (encPair (encSum encNat encZ) encBool))))
    (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))))
  have hrev := (ComputableTidilyInPolyTime.listReverse
    (encList (encPair (encSum encNat (encSum encY encZ)) encBool))).computableInPolyTime
  have hzip := (ComputableTidilyInPolyTime.zipIdx
    (encList (encPair (encSum encNat (encSum encY encZ)) encBool))).computableInPolyTime
  have htake := (ComputableTidilyInPolyTime.takeUnary
    (encList (encPair (encSum encNat (encSum encY encZ)) encBool))).computableInPolyTime
  have hbin := ComputableTidilyInPolyTime.unary_to_binary.computableInPolyTime
  have hlines := hrev.comp hp.snd'.snd'
  -- the gates, line by line
  have hgates := flatMapWithInput (f := fun (p : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
      List (Clause (ℕ ⊕ (Y ⊕ Z)))) (e : Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) =>
        Interpolant.lineGates p.1 p.2.1.1 p.2.1.2 (p.2.2.reverse.take e.2) e.1)
    (hzip.comp hlines) (Interpolant.lineGates_polyTime.comp
      (((fst _ _).fst'.prod (fst _ _).snd'.fst').prod
        ((htake.comp ((hlines.comp (fst _ _)).prod (snd _ _).snd')).prod (snd _ _).fst')))
  -- the output wire
  have hempty := mapWithInput (f := fun (_ : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
      List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) => c.isEmpty) hlines
    ((ComputableTidilyInPolyTime.listIsEmpty'
      (encPair (encSum encNat (encSum encY encZ)) encBool)).computableInPolyTime.comp (snd _ _))
  have hidx := (ComputableTidilyInPolyTime.idxOf encBool).computableInPolyTime.comp
    (hempty.prod (const true))
  have hout := hbin.comp (unary_add' (unary_add' hp.fst' (unary_mul' (const 4) hidx)) (const 3))
  exact hgates.prod (cons' hout (const []))

/-! ### The monotone interpolant -/

namespace MonotoneInterpolant

variable {encY : Y ↪ List Bool} {encZ : Z ↪ List Bool}

omit [DecidableEq Y] [DecidableEq Z] in
/-- The gates of a resolution step, by option elimination on the variable. -/
private theorem resolventGates_eq (pos : Bool) (base w₁ w₂ : ℕ) (v : ℕ ⊕ (Y ⊕ Z)) :
    resolventGates pos base w₁ w₂ v =
      v.getLeft?.elim
        (if v.getRight?.elim false Sum.isLeft then padGate (.or, [w₁, w₂])
          else padGate (.and, [w₁, w₂]))
        fun i => if pos then [(.or, [i, w₁]), (.and, [base, w₂])]
          else [(.and, [i, w₂]), (.or, [base, w₁])] := by
  rcases v with _ | _ | _ <;> rfl

/-- Two binary monotone gates on computed wires. -/
private theorem twoGates {γ : Type} {encIn : γ ↪ List Bool} (op₁ op₂ : Monotone.Op)
    {u₁ u₂ v₁ v₂ : γ → ℕ} (hu₁ : ComputableInPolyTime u₁ encIn encNat)
    (hu₂ : ComputableInPolyTime u₂ encIn encNat) (hv₁ : ComputableInPolyTime v₁ encIn encNat)
    (hv₂ : ComputableInPolyTime v₂ encIn encNat) :
    ComputableInPolyTime (fun x => [(op₁, [u₁ x, u₂ x]), (op₂, [v₁ x, v₂ x])]) encIn
      (encList Monotone.encGate) :=
  cons' ((const op₁).prod (cons' hu₁ (cons' hu₂ (const []))))
    (cons' ((const op₂).prod (cons' hv₁ (cons' hv₂ (const [])))) (const []))

/-- A constant gate before a binary monotone gate on computed wires. -/
private theorem padGate_binary {γ : Type} {encIn : γ ↪ List Bool} (op : Monotone.Op)
    {w₁ w₂ : γ → ℕ} (h₁ : ComputableInPolyTime w₁ encIn encNat)
    (h₂ : ComputableInPolyTime w₂ encIn encNat) :
    ComputableInPolyTime (fun x => padGate (op, [w₁ x, w₂ x])) encIn
      (encList Monotone.encGate) := by
  unfold padGate
  exact cons' (const _) (cons' ((const op).prod (cons' h₁ (cons' h₂ (const [])))) (const []))

omit [DecidableEq Y] [DecidableEq Z] in
/-- The gates of a monotone resolution step are computed in polynomial time from the polarity,
the wires, in binary, and the variable. -/
private theorem resolventGates_polyTime :
    ComputableInPolyTime (fun r : (Bool × ℕ × ℕ × ℕ) × (ℕ ⊕ (Y ⊕ Z)) =>
        resolventGates r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 r.2)
      (encPair (encPair encBool (encPair encNat (encPair encNat encNat)))
        (encSum encNat (encSum encY encZ)))
      (encList Monotone.encGate) := by
  simp only [resolventGates_eq]
  have hr := id' (encIn := encPair (encPair encBool (encPair encNat (encPair encNat encNat)))
    (encSum encNat (encSum encY encZ)))
  have hv := hr.snd'
  have hw₁ := hr.fst'.snd'.snd'.fst'
  have hw₂ := hr.fst'.snd'.snd'.snd'
  refine optionElimWithInput ((Interpolant.getLeft? _ _).comp hv)
    (ite (optionElimWithInput ((Interpolant.getRight? _ _).comp hv) (const false)
      ((Interpolant.isLeft _ _).comp (snd _ _))) (padGate_binary _ hw₁ hw₂)
      (padGate_binary _ hw₁ hw₂)) ?_
  have hq := fst (encPair (encPair encBool (encPair encNat (encPair encNat encNat)))
    (encSum encNat (encSum encY encZ))) encNat
  have hi := snd (encPair (encPair encBool (encPair encNat (encPair encNat encNat)))
    (encSum encNat (encSum encY encZ))) encNat
  have hbase := hq.fst'.snd'.fst'
  exact ite hq.fst'.fst' (twoGates _ _ hi hq.fst'.snd'.snd'.fst' hbase hq.fst'.snd'.snd'.snd')
    (twoGates _ _ hi hq.fst'.snd'.snd'.snd' hbase hq.fst'.snd'.snd'.fst')

omit [DecidableEq Y] [DecidableEq Z] in
/-- The polarity test is polynomial-time. -/
private theorem positive_polyTime :
    ComputableInPolyTime (positive (X := ℕ) (Y := Y))
      (encList (encList (encPair (encSum encNat encY) encBool))) encBool := by
  have hlit : ComputableInPolyTime
      (fun p : (CNF (ℕ ⊕ Y) × Clause (ℕ ⊕ Y)) × Literal (ℕ ⊕ Y) => p.2.1.isRight || p.2.2)
      (encPair (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
        (encList (encPair (encSum encNat encY) encBool))) (encPair (encSum encNat encY) encBool))
      encBool :=
    ComputableTidilyInPolyTime.bool_or.computableInPolyTime.comp
      (((ComputableInO.isRight_deg encNat encY).computableInPolyTime.comp (snd _ _).fst').prod
        (snd _ _).snd')
  exact allWithEncoding (test := fun p : CNF (ℕ ⊕ Y) × Clause (ℕ ⊕ Y) =>
    p.2.all fun l => l.1.isRight || l.2) (allWithEncoding hlit id' (snd _ _)) id' id'

/-- The two gates of a line are computed in polynomial time from the number of inputs in unary,
the two formulas, the earlier lines and the line. -/
private theorem lineGates_polyTime :
    ComputableInPolyTime (fun q : (ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z))) ×
        (List (Clause (ℕ ⊕ (Y ⊕ Z))) × Clause (ℕ ⊕ (Y ⊕ Z))) =>
          lineGates (positive q.1.2.1) q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2)
      (encPair (encPair encUnary (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
          (encList (encList (encPair (encSum encNat encZ) encBool)))))
        (encPair (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))
          (encList (encPair (encSum encNat (encSum encY encZ)) encBool))))
      (encList Monotone.encGate) := by
  have hq := id' (encIn := encPair (encPair encUnary
    (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
      (encList (encList (encPair (encSum encNat encZ) encBool)))))
    (encPair (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))
      (encList (encPair (encSum encNat (encSum encY encZ)) encBool))))
  have hc := hq.snd'.snd'
  have hE := hq.snd'.fst'
  have hmemA := decide_mem ((CNF.computableInPolyTime_relabel
    (Interpolant.sumMap_inl (encZ := encZ))).comp hq.fst'.snd'.fst') hc
  have hmemB := decide_mem ((CNF.computableInPolyTime_relabel
    (Interpolant.sumMap_inr (encY := encY))).comp hq.fst'.snd'.snd') hc
  have hbin := ComputableTidilyInPolyTime.unary_to_binary.computableInPolyTime
  -- the search for a resolution step deriving the line
  have hp := id' (encIn := encPair (encPair (encPair encUnary
    (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
      (encList (encList (encPair (encSum encNat encZ) encBool)))))
    (encPair (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))
      (encList (encPair (encSum encNat (encSum encY encZ)) encBool))))
    (encPair (encPair (encList (encPair (encSum encNat (encSum encY encZ)) encBool)) encUnary)
      (encPair (encPair (encList (encPair (encSum encNat (encSum encY encZ)) encBool)) encUnary)
        (encSum encNat (encSum encY encZ)))))
  have hc₁ := hp.snd'.fst'.fst'
  have hc₂ := hp.snd'.snd'.fst'.fst'
  have hv := hp.snd'.snd'.snd'
  have htest := decide_and (decide_mem hc₁ (hv.prod (const true)))
    (decide_and (decide_mem hc₂ (hv.prod (const false)))
      (decide_eq' (Interpolant.resolvent_polyTime.comp ((hc₁.prod hc₂).prod hv))
        hp.fst'.snd'.snd'))
  have hfind := findWithInput (test := fun q t => decide ((t.2.2, true) ∈ t.1.1 ∧
    (t.2.2, false) ∈ t.2.1.1 ∧ t.1.1.resolvent t.2.1.1 t.2.2 = q.2.2))
    (Interpolant.candidates_polyTime.comp hE) htest
  -- the gates of the step found
  have hm := hp.fst'.fst'.fst'
  have hbody := resolventGates_polyTime.comp
      (((positive_polyTime.comp hp.fst'.fst'.snd'.fst').prod
      ((hbin.comp (unary_add' hm (unary_mul' (const 2)
        ((length_list _).comp hp.fst'.snd'.fst')))).prod
      ((hbin.comp (unary_add' (unary_add' hm (unary_mul' (const 2) hp.snd'.fst'.snd'))
        (const 1))).prod
      (hbin.comp (unary_add' (unary_add' hm (unary_mul' (const 2) hp.snd'.snd'.fst'.snd'))
        (const 1)))))).prod hv)
  unfold lineGates
  exact ite_decide hmemA (const _) (ite_decide hmemB (const _)
    (optionElimWithInput (body := fun (q : (ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z))) ×
        (List (Clause (ℕ ⊕ (Y ⊕ Z))) × Clause (ℕ ⊕ (Y ⊕ Z))))
        (t : (Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) × (Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) × (ℕ ⊕ (Y ⊕ Z))) =>
      resolventGates (positive q.1.2.1) (q.1.1 + 2 * q.2.1.length) (q.1.1 + 2 * t.1.2 + 1)
        (q.1.1 + 2 * t.2.1.2 + 1) t.2.2) hfind (const _) hbody))

end MonotoneInterpolant

/-- **Extracting monotone interpolants in polynomial time.** The code of the monotone interpolant
circuit of a resolution refutation (`Cslib.Logic.PL.CNF.monotoneInterpolantCode`) is computed in
polynomial time from the number of inputs in unary, the two formulas and the lines of the
refutation, encoded as for `Cslib.Logic.PL.CNF.computableInPolyTime_interpolantCode`; the circuit
code is written in the binary encoding `Cslib.Circuits.Monotone.encCode`. On a refutation whose
shared variables occur only positively in `A` or only negatively in `B`, the code is that of a
monotone circuit computing an interpolant
(`Cslib.Logic.PL.CNF.IsProof.ofCode_monotoneInterpolantCode`). -/
theorem CNF.computableInPolyTime_monotoneInterpolantCode (encY : Y ↪ List Bool)
    (encZ : Z ↪ List Bool) :
    ComputableInPolyTime (fun ((n, (A, B), ls) : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
        List (Clause (ℕ ⊕ (Y ⊕ Z)))) => CNF.monotoneInterpolantCode n A B ls)
      (encPair encUnary (encPair (encPair (encList (encList (encPair (encSum encNat encY) encBool)))
        (encList (encList (encPair (encSum encNat encZ) encBool))))
        (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))))
      Monotone.encCode := by
  have hp := id' (encIn := encPair encUnary (encPair (encPair
    (encList (encList (encPair (encSum encNat encY) encBool)))
    (encList (encList (encPair (encSum encNat encZ) encBool))))
    (encList (encList (encPair (encSum encNat (encSum encY encZ)) encBool)))))
  have hrev := (ComputableTidilyInPolyTime.listReverse
    (encList (encPair (encSum encNat (encSum encY encZ)) encBool))).computableInPolyTime
  have hzip := (ComputableTidilyInPolyTime.zipIdx
    (encList (encPair (encSum encNat (encSum encY encZ)) encBool))).computableInPolyTime
  have htake := (ComputableTidilyInPolyTime.takeUnary
    (encList (encPair (encSum encNat (encSum encY encZ)) encBool))).computableInPolyTime
  have hbin := ComputableTidilyInPolyTime.unary_to_binary.computableInPolyTime
  have hlines := hrev.comp hp.snd'.snd'
  -- the gates, line by line
  have hgates := flatMapWithInput (f := fun (p : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
      List (Clause (ℕ ⊕ (Y ⊕ Z)))) (e : Clause (ℕ ⊕ (Y ⊕ Z)) × ℕ) =>
        MonotoneInterpolant.lineGates (MonotoneInterpolant.positive p.2.1.1) p.1 p.2.1.1 p.2.1.2
          (p.2.2.reverse.take e.2) e.1)
    (hzip.comp hlines) (MonotoneInterpolant.lineGates_polyTime.comp
      (((fst _ _).fst'.prod (fst _ _).snd'.fst').prod
        ((htake.comp ((hlines.comp (fst _ _)).prod (snd _ _).snd')).prod (snd _ _).fst')))
  -- the output wire
  have hempty := mapWithInput (f := fun (_ : ℕ × (CNF (ℕ ⊕ Y) × CNF (ℕ ⊕ Z)) ×
      List (Clause (ℕ ⊕ (Y ⊕ Z)))) (c : Clause (ℕ ⊕ (Y ⊕ Z))) => c.isEmpty) hlines
    ((ComputableTidilyInPolyTime.listIsEmpty'
      (encPair (encSum encNat (encSum encY encZ)) encBool)).computableInPolyTime.comp (snd _ _))
  have hidx := (ComputableTidilyInPolyTime.idxOf encBool).computableInPolyTime.comp
    (hempty.prod (const true))
  have hout := hbin.comp (unary_add' (unary_add' hp.fst' (unary_mul' (const 2) hidx)) (const 1))
  exact hgates.prod (cons' hout (const []))

end Cslib.Logic.PL
