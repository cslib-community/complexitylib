/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.WeightedComparison.Family
public import CslibFrontier.Logics.Propositional.CNF.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval
import Mathlib.Data.List.GetD

/-!
# Actual polynomial-weight tests on an existing DNF counting instance

Append the proved functional tests to the actual original side CNF, retaining all predicates and
original declared variables. This is Corollary A.2's construction, not a supplied constructor.
The proof-only existing CNF lifting lemma is reused; it does not introduce graph hypotheses.
Source: [ChenJiangZhu2027], Corollary A.2, PDF p.29.

## Main results

* `build_polytime`: actual existing-instance augmentation, including all copied predicates.
* `representation`: finite formulas, width bounds and exact correlated original count.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum.WithBase

open Turing.MultiTapeTM Logic.PL

/-- Original explicit DNF counting instance and runtime coefficient/polarity/target rows. -/
abbrev Input := TwoBoundary.BinaryFrontend.Input × (List (List (ℕ × Bool)) × List ℤ)
/-- Original instance, preserving declared unused bits and all original annotations. -/
@[expose] def original (x : Input) := x.1
/-- Actual weighted-test frame shares precisely the original instance's declared inputs. -/
@[expose] def frame (x : Input) : Family.Input :=
  (TwoBoundary.BinaryFrontend.declared (original x), x.2)
/-- Complete original binary frame, with no supplied gate count, normalized circuit or output. -/
abbrev encInput := encPair TwoBoundary.BinaryFrontend.encInput
  (encPair (encList (encList (encPair encNat encBool))) (encList encIntBin))
/-- Actual computed gate count, charged by the original-input generator. -/
@[expose] def auxiliary {r : ℕ} (op : Fin r → Comparison) (c : ℕ) (x : Input) : ℕ :=
  (Family.code op c (frame x)).1.length
/-- Append full functional clauses, keeping original predicates/references on input wires. -/
@[expose] def build {r : ℕ} (op : Fin r → Comparison) (c : ℕ) (x : Input) :
    TwoBoundary.BinaryFrontend.Input :=
  (TwoBoundary.BinaryFrontend.declared (original x) + auxiliary op c x,
    TwoBoundary.BinaryFrontend.side (original x) ++ Family.build op c (frame x),
    TwoBoundary.BinaryFrontend.conditions (original x))
/-- Canonical original finite formulas and runtime weighted tests on their same original bits. -/
@[expose] def ofData {n r : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ) : Input :=
  (TwoBoundary.BinaryFrontend.ofFinite B P,
    (Family.rows (Family.ofData weights positive target),
      Family.targets (Family.ofData weights positive target)))

/-- Actual ordinary query count of the augmented instance: original predicates determine
whether one query or a pair is needed; functional tests do not add annotations. -/
theorem query_count {r : ℕ} (op : Fin r → Comparison) (c : ℕ) (x : Input) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build op c x))).length =
      (if (TwoBoundary.BinaryFrontend.conditions (original x)).isEmpty then 1 else 2) :=
  TwoBoundary.BinaryFrontend.compile_query_count (build op c x)

private theorem frame_polytime : ComputableInPolyTime frame encInput Family.encInput := by
  unfold frame original encInput Family.encInput TwoBoundary.BinaryFrontend.encInput
    TwoBoundary.BinaryFrontend.declared
  fun_prop

/-- Every gate-count computation, side append and original predicate copy is charged in bit time. -/
@[fun_prop] theorem build_polytime {r : ℕ} (op : Fin r → Comparison) (c : ℕ) :
    ComputableInPolyTime (build op c) encInput TwoBoundary.BinaryFrontend.encInput := by
  have hf := frame_polytime
  have hg := (Family.code_polytime op c).comp hf
  have ha := (ComputableInPolyTime.length_list encGate).comp hg.fst'
  have hside := (Family.build_polytime op c).comp hf
  unfold build auxiliary TwoBoundary.BinaryFrontend.encInput
  have hn : ComputableInPolyTime
      (fun x : Input => TwoBoundary.BinaryFrontend.declared (original x)) encInput encUnary := by
    unfold original encInput TwoBoundary.BinaryFrontend.encInput TwoBoundary.BinaryFrontend.declared
    fun_prop
  have hb : ComputableInPolyTime
      (fun x : Input => TwoBoundary.BinaryFrontend.side (original x)) encInput
      (encList (encList (encPair encNat encBool))) := by
    unfold original encInput TwoBoundary.BinaryFrontend.encInput TwoBoundary.BinaryFrontend.side
    fun_prop
  have hp : ComputableInPolyTime
      (fun x : Input => TwoBoundary.BinaryFrontend.conditions (original x)) encInput
      (encList (encList (encList (encPair encNat encBool)))) := by
    unfold original encInput TwoBoundary.BinaryFrontend.encInput
      TwoBoundary.BinaryFrontend.conditions
    fun_prop
  exact (ComputableInPolyTime.unary_add.comp (hn.prod ha)).prod
    ((ComputableInPolyTime.listAppend' hb hside).prod hp)

private theorem canonical_frame {n r : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ) :
    frame (ofData B P weights positive target) = Family.ofData weights positive target := rfl

/-- Actual original data computes the approved joint circuit's full gate count. -/
theorem auxiliary_ofData {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (B : CNF (Fin n)) (P : List (DNF (Fin n))) (weights : Fin r → Fin n → ℕ)
    (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ) :
    auxiliary op c (ofData B P weights positive target) =
      (joint op c weights positive target).size := by
  unfold auxiliary
  rw [canonical_frame]
  rw [Family.code_ofData]
  exact Circuit.length_code_fst _

open Classical in
/-- Finite presentation of the actual appended construction, preserving every original predicate
and its annotation multiplicity. The functional gates are computed, not supplied as advice. -/
theorem representation {n r b d : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (B : CNF (Fin n)) (P : List (DNF (Fin n))) (weights : Fin r → Fin n → ℕ)
    (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ)
    (hw : ∀ j i, weights j i ≤ n ^ c)
    (hb : ∀ clause ∈ B, clause.length ≤ b) (hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d) :
    let a := (joint op c weights positive target).size
    ∃ BF : CNF (Fin (n + a)), ∃ PF : List (DNF (Fin (n + a))),
      build op c (ofData B P weights positive target) = TwoBoundary.BinaryFrontend.ofFinite BF PF ∧
      (∀ clause ∈ BF, clause.length ≤ max b 3) ∧
      (∀ p ∈ PF, ∀ t ∈ p, t.length ≤ d) ∧ PF.length = P.length ∧
      Fintype.card {y : Fin (n + a) → Bool // BF.eval y = true ∧ ∀ p ∈ PF, DNF.eval y p = true} =
        Fintype.card {x : Fin n → Bool //
          (∀ j, (op j).Holds (value (weights j) (positive j) x) (target j)) ∧
          B.eval x = true ∧ ∀ p ∈ P, DNF.eval x p = true} := by
  let a := (joint op c weights positive target).size
  let ι : Fin n → Fin (n + a) := Fin.castAdd a
  obtain ⟨F, hF⟩ := IndependentDominationInterval.lift_cnf
    (jointFormula op c weights positive target) (fun clause hcl =>
      (FunctionalCNF.write_bounds _ _ clause hcl).2)
  let BF := B.relabel ι ++ F
  let PF := P.map (CNF.relabel ι)
  have herase (D : CNF (Fin n)) : (D.relabel ι).relabel Fin.val = D.relabel Fin.val := by
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    congr 1
  have hside : BF.relabel Fin.val =
      B.relabel Fin.val ++ jointFormula op c weights positive target := by
    change ((B.relabel ι) ++ F).map (Clause.relabel Fin.val) = _
    rw [List.map_append]
    change (B.relabel ι).relabel Fin.val ++ F.relabel Fin.val = _
    rw [herase, hF]
  have hpred : PF.map (CNF.relabel Fin.val) = P.map (CNF.relabel Fin.val) := by
    simp only [PF, List.map_map, Function.comp_def, herase]
  refine ⟨BF, PF, ?_, ?_, ?_, by simp only [PF, List.length_map], ?_⟩
  · dsimp only [build]
    rw [auxiliary_ofData, canonical_frame, Family.build_ofData]
    change (n + a, B.relabel Fin.val ++ jointFormula op c weights positive target,
      P.map (CNF.relabel Fin.val)) =
        (n + a, BF.relabel Fin.val, PF.map (CNF.relabel Fin.val))
    exact Prod.ext rfl (Prod.ext hside.symm hpred.symm)
  · intro clause hcl
    rcases List.mem_append.mp hcl with hcl | hcl
    · obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hcl
      simpa only [Clause.relabel, List.length_map] using
        (hb old ho).trans (le_max_left b 3)
    · have hc : clause.relabel Fin.val ∈ jointFormula op c weights positive target := by
        rw [← hF]
        exact List.mem_map.mpr ⟨clause, hcl, rfl⟩
      have hl := (FunctionalCNF.write_bounds _ _ _ hc).1
      simp only [Clause.relabel, List.length_map] at hl
      exact hl.le.trans (le_max_right _ _)
  · intro p hpm t htm
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hpm
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp htm
    simpa only [Clause.relabel, List.length_map] using hp p0 hp0 t0 ht0
  · simp only [← Nat.card_eq_fintype_card]
    have hPred (y : Fin (n + a) → Bool) :
        BF.eval y = true ∧ (∀ p ∈ PF, DNF.eval y p = true) ↔
        (jointFormula op c weights positive target).eval
          (Function.extend Fin.val y (fun _ => false)) = true ∧
          (B.eval (y ∘ ι) = true ∧ ∀ p ∈ P, DNF.eval (y ∘ ι) p = true) := by
      have hf : F.eval y = (jointFormula op c weights positive target).eval
          (Function.extend Fin.val y (fun _ => false)) := by
        rw [← hF, CNF.eval_relabel, Function.extend_comp Fin.val_injective]
      simp only [BF, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, hf,
        PF, List.forall_mem_map, DNF.eval_relabel]
      tauto
    calc _ = Nat.card {y : Fin (n + a) → Bool //
        (jointFormula op c weights positive target).eval
          (Function.extend Fin.val y (fun _ => false)) = true ∧
          (B.eval (y ∘ ι) = true ∧ ∀ p ∈ P, DNF.eval (y ∘ ι) p = true)} :=
            Nat.card_congr (Equiv.subtypeEquivRight hPred)
      _ = _ := by
        simpa only [← Nat.card_eq_fintype_card, Function.comp_def] using
          count_jointFormula op c weights positive target hw
            (fun x => B.eval x = true ∧ ∀ p ∈ P, DNF.eval x p = true)

end Cslib.Circuits.Boolean.WeightedSum.WithBase
