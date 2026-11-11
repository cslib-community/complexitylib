/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Space
public import CslibFrontier.Computability.Complexity.Classes.Space.Closure
public import CslibFrontier.Computability.Complexity.Problems.SharpSAT
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# SAT, UNSAT, USAT, and #SAT in polynomial space

Enumerating all `2 ^ φ.numVars` assignments to `φ.distinctVars` in a single workspace of
polynomial size computes `SharpSAT φ` in polynomial space
(`Cslib.Complexity.SharpSAT.computableInPolySpace_numVars`), reusing
`Cslib.Complexity.streamAcceptCount` and `Cslib.Complexity.computableInPolySpace_acceptCount`.

Unlike `Cslib.Complexity.SharpSAT.mem_SharpP` (which pads certificates to `|(encCNF φ)|` bits so
that arbitrary polynomial witnesses share the same verifier contract), the enumeration here uses
`φ.numVars`-bit certificates indexed by `φ.distinctVars` (`Cslib.Complexity.SAT.distinctVerifier`),
matching the `2 ^ φ.numVars` enumeration bound. Testing positivity (`0 < #SAT`) or uniqueness
(`#SAT = 1`) on the resulting binary count places `SAT`, `UNSAT`, and `USAT` in `PSPACE encCNF`
directly by deterministic space-bounded enumeration.

## Main definitions

* `Cslib.Complexity.SAT.distinctVerifier`: evaluate a CNF formula on a certificate indexed by
  `φ.distinctVars`.

## Main results

* `Cslib.Complexity.SAT.acceptCount_distinctVerifier`,
  `Cslib.Complexity.SAT.streamAcceptCount_distinctVerifier_eq`: enumerating `2 ^ φ.numVars`
  binary assignments via `distinctVerifier` computes `SharpSAT φ`.
* `Cslib.Complexity.SAT.computableInPolyTime_distinctVerifier`: `distinctVerifier` is
  polynomial-time.
* `Cslib.Complexity.SharpSAT.computableInPolySpace_numVars`,
  `Cslib.Complexity.SharpSAT.exists_computableInSpace_numVars`: `#SAT` is computable in
  polynomial space.
* `Cslib.Complexity.SAT.mem_PSPACE_of_enumeration`,
  `Cslib.Complexity.UNSAT.mem_PSPACE_of_enumeration`,
  `Cslib.Complexity.USAT.mem_PSPACE_of_enumeration`: `SAT`, `UNSAT`, and `USAT` lie in
  `PSPACE encCNF` by deterministic polynomial-space enumeration.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SAT

/-- The distinct-variable verifier for `SAT` and `#SAT`: read each variable's Boolean value from
the bit of the certificate `w` at its index in `φ.distinctVars`. On `φ.numVars`-bit
certificates, each satisfying assignment corresponds to a unique certificate. -/
@[expose] def distinctVerifier (x : CNF ℕ × List Bool) : Bool :=
  x.1.eval fun v => x.2.getD (x.1.distinctVars.idxOf v) false

/-- Enumerating `φ.numVars`-bit certificates against `distinctVerifier` counts the satisfying
assignments `SharpSAT φ`. -/
theorem acceptCount_distinctVerifier (φ : CNF ℕ) :
    acceptCount distinctVerifier φ φ.numVars = SharpSAT φ := by
  symm
  rw [SharpSAT, acceptCount]
  set vs := φ.distinctVars
  have hnd : vs.Nodup := CNF.nodup_distinctVars φ
  have hlen : vs.length = φ.numVars := CNF.length_distinctVars φ
  refine CNF.modelCount_eq_card_filter
    (fun σ (i : Fin φ.numVars) => σ (vs[i.1]'(by rw [hlen]; exact i.2)))
    (fun w => distinctVerifier (φ, List.ofFn w) = true)
    (fun σ τ _ _ => ⟨fun h v hv => ?_, fun h => funext fun i => h _ (by
      exact CNF.mem_distinctVars.1 (List.getElem_mem (by rw [hlen]; exact i.2)))⟩)
    fun w => ⟨fun hw => ?_, ?_⟩
  · have hmem : v ∈ vs := CNF.mem_distinctVars.2 hv
    have hlt : vs.idxOf v < φ.numVars := by
      rw [← hlen]
      exact List.idxOf_lt_length_iff.2 hmem
    have hcon := congrFun h ⟨vs.idxOf v, hlt⟩
    simpa only [List.getElem_idxOf] using hcon
  · refine ⟨fun v => (List.ofFn w).getD (vs.idxOf v) false, hw, funext fun i => ?_⟩
    have hlt : i.1 < vs.length := by rw [hlen]; exact i.2
    dsimp only
    rw [hnd.idxOf_getElem i.1 hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.2, ↓reduceDIte, Option.getD_some]
  · rintro ⟨σ, hσ, rfl⟩
    refine (CNF.eval_congr fun v hv => ?_).trans hσ
    have hmem : v ∈ vs := CNF.mem_distinctVars.2 hv
    have hltvs : vs.idxOf v < vs.length := List.idxOf_lt_length_iff.2 hmem
    have hlt : φ.distinctVars.idxOf v < φ.numVars := by rwa [← hlen]
    dsimp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hlt, ↓reduceDIte, Option.getD_some]
    exact congrArg σ (List.getElem_idxOf hltvs)

/-- Streaming `2 ^ φ.numVars` steps of `distinctVerifier` computes `SharpSAT φ`. -/
theorem streamAcceptCount_distinctVerifier_eq (φ : CNF ℕ) :
    streamAcceptCount distinctVerifier φ φ.numVars = SharpSAT φ :=
  (streamAcceptCount_eq_acceptCount distinctVerifier φ φ.numVars).trans
    (acceptCount_distinctVerifier φ)

/-- `distinctVerifier` is computable in polynomial time on encoded formulas and certificates. -/
@[fun_prop]
theorem computableInPolyTime_distinctVerifier :
    ComputableInPolyTime distinctVerifier (encPair encCNF encBits) encBool := by
  fun_prop [distinctVerifier]

end SAT

namespace SharpSAT

/-- **`#SAT` is computable in polynomial space** by streaming `2 ^ φ.numVars` assignments via
`SAT.distinctVerifier` and `streamAcceptCount`. -/
theorem computableInPolySpace_numVars :
    ComputableInPolySpace SharpSAT encCNF encNat := by
  have h : (fun φ : CNF ℕ => acceptCount SAT.distinctVerifier φ φ.numVars) = SharpSAT :=
    funext SAT.acceptCount_distinctVerifier
  rw [← h]
  exact computableInPolySpace_acceptCount SAT.computableInPolyTime_distinctVerifier
    SAT.computableInPolyTime_numVars

/-- Explicit space certificate for `SharpSAT`: there is a polynomially bounded space bound `S`
such that `SharpSAT` is computable in space `S`. -/
theorem exists_computableInSpace_numVars :
    ∃ S, PolyBounded (fun φ => (encCNF φ).length) S ∧
      ComputableInSpace SharpSAT encCNF encNat S :=
  computableInPolySpace_numVars.exists_inSpace

end SharpSAT

/-- `SAT` lies in `PSPACE encCNF` by deterministic polynomial-space enumeration of all
`2 ^ φ.numVars` assignments. -/
theorem SAT.mem_PSPACE_of_enumeration : SAT ∈ PSPACE encCNF := by
  refine mem_PSPACE_of_computableInPolySpace (f := fun φ : CNF ℕ => decide (0 < SharpSAT φ))
    ?_ fun φ => by rw [SharpSAT.mem_SAT_iff, decide_eq_true_eq]
  have hpos : ComputableInPolyTime (fun n : ℕ => decide (0 < n)) encNat encBool := by fun_prop
  exact (ComputableInPolySpace.of_polyTime hpos).comp SharpSAT.computableInPolySpace_numVars

/-- `UNSAT` lies in `PSPACE encCNF` by deterministic polynomial-space enumeration. -/
theorem UNSAT.mem_PSPACE_of_enumeration : UNSAT ∈ PSPACE encCNF :=
  compl_SAT ▸ compl_mem_PSPACE SAT.mem_PSPACE_of_enumeration

/-- `USAT` lies in `PSPACE encCNF` by deterministic polynomial-space enumeration and checking
`#SAT = 1`. -/
theorem USAT.mem_PSPACE_of_enumeration : USAT ∈ PSPACE encCNF := by
  refine mem_PSPACE_of_computableInPolySpace
    (f := fun φ : CNF ℕ => decide (0 < SharpSAT φ) && decide (SharpSAT φ < 2)) ?_ fun φ => by
    rw [SharpSAT.mem_USAT_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega
  have heq1 : ComputableInPolyTime (fun n : ℕ => decide (0 < n) && decide (n < 2))
      encNat encBool := by fun_prop
  exact (ComputableInPolySpace.of_polyTime heq1).comp SharpSAT.computableInPolySpace_numVars

end Cslib.Complexity
