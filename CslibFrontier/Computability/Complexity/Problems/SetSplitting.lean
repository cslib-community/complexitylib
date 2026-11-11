/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.CNF.GraphCountingEncodings
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen

/-!
# Set splitting

`SetSplitting` is the set-splitting decision problem (Garey and Johnson SP4; equivalently hypergraph
`2`-colorability): given a declared ground list `ground : List ℕ` and a family
`sets : List (List ℕ)`, does `ground.toFinset` admit a bipartition `(A, B)` such that every subset
`s ∈ sets` intersects both `A` and `B`?

Reusing `Cslib.Logic.PL.CNF.setSplittingCNF`, every valid instance compiles in polynomial time
with clause width bounded by the maximum set size `k` and declared variable range `|U|`
(`SetSplittingInstance.toDeclaredCNF`), preserving the exact number of ordered splitting
bipartitions `SetSplittingInstance.count`.

## Main definitions

* `Cslib.Complexity.SetSplittingInstance`, `Cslib.Complexity.encSetSplitting`: instances and
  binary encoding.
* `Cslib.Complexity.SetSplitting`: decision problem (`SetSplitting ∈ NP encSetSplitting`).
* `Cslib.Complexity.SetSplittingInstance.Valid`,
  `Cslib.Complexity.SetSplittingInstance.validBool`,
  `Cslib.Complexity.SetSplittingInstance.maxSetSizeBool`: validity and set-size guards.
* `Cslib.Complexity.SetSplittingInstance.count`: exact number of ordered splitting bipartitions.
* `Cslib.Complexity.SetSplittingInstance.toCNF`,
  `Cslib.Complexity.SetSplittingInstance.toDeclaredCNF`: width-`≤ k` CNF compilations on `|U|`
  variables.

## Main results

* `Cslib.Complexity.SetSplitting.mem_NP`: `SetSplitting ∈ NP encSetSplitting`.
* `Cslib.Complexity.SetSplittingInstance.toCNFEquiv`,
  `Cslib.Complexity.SetSplittingInstance.modelCountOn_toCNF`,
  `Cslib.Complexity.SetSplittingInstance.modelCountOn_toDeclaredCNF`: exact model-count
  preservation (`= x.count`) with clause width `≤ k`.
* `Cslib.Complexity.SetSplittingInstance.computableInPolyTime_toCNF`,
  `Cslib.Complexity.SetSplittingInstance.computableInPolyTime_toDeclaredCNF`: polynomial-time
  compilations.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- An instance of **set splitting**: a declared ground list `ground` and a family `sets` of
subsets over `ℕ` (Garey and Johnson SP4). -/
structure SetSplittingInstance where
  /-- The declared ground list of elements. -/
  ground : List ℕ
  /-- The family of subsets that must each intersect both sides of the bipartition. -/
  sets : List (List ℕ)
  deriving DecidableEq, Repr

/-- Binary encoding of a set-splitting instance as its framed element list followed by its framed
family of subsets. -/
enc_structure encSetSplitting : SetSplittingInstance where
  ground : (encList encNat), sets : (encList (encList encNat))

attribute [fun_prop] encSetSplitting_ground_polyTime encSetSplitting_sets_polyTime
  encSetSplitting_mk_polyTime

/-- **Set splitting** [GareyJohnson1979]: there is a subset `A ⊆ ground` such that every subset
`s ∈ sets` contains an element of `A` and an element of `ground \ A`. -/
@[expose] def SetSplitting : Set SetSplittingInstance :=
  {x | ∃ A : Finset ℕ, (∀ v ∈ A, v ∈ x.ground) ∧
    ∀ s ∈ x.sets, (∃ u ∈ s, u ∈ A) ∧ (∃ v ∈ s, v ∈ x.ground ∧ v ∉ A)}

/-- Equivalent formulation in terms of ordered splitting bipartitions `(A, B)` of
`x.ground.toFinset`. -/
theorem mem_SetSplitting_iff_bipartition {x : SetSplittingInstance} :
    x ∈ SetSplitting ↔
      ∃ A B : Finset ℕ, A ∪ B = x.ground.toFinset ∧ Disjoint A B ∧
        ∀ s ∈ x.sets, (∃ u ∈ s, u ∈ A) ∧ (∃ v ∈ s, v ∈ B) := by
  classical
  constructor
  · rintro ⟨A, hAU, hsp⟩
    refine ⟨A, x.ground.toFinset \ A, Finset.union_sdiff_of_subset
      (fun v hv => List.mem_toFinset.mpr (hAU v hv)), disjoint_sdiff_self_right, ?_⟩
    intro s hs
    obtain ⟨⟨u, hu, huA⟩, ⟨v, hv, hvU, hvA⟩⟩ := hsp s hs
    exact ⟨⟨u, hu, huA⟩, ⟨v, hv, Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hvU, hvA⟩⟩⟩
  · rintro ⟨A, B, hAB, hdisj, hsp⟩
    refine ⟨A, fun v hv => List.mem_toFinset.mp (hAB ▸ Finset.mem_union_left B hv), ?_⟩
    intro s hs
    obtain ⟨⟨u, hu, huA⟩, ⟨v, hv, hvB⟩⟩ := hsp s hs
    have hvU : v ∈ x.ground :=
      List.mem_toFinset.mp (hAB ▸ Finset.mem_union_right A hvB)
    exact ⟨⟨u, hu, huA⟩, ⟨v, hv, hvU, Finset.disjoint_right.mp hdisj hvB⟩⟩

namespace SetSplitting

/-- Check a candidate subset `A` of the declared ground set: every `s ∈ x.sets` meets both `A` and
`x.ground \ A`. -/
@[expose] def check (x : SetSplittingInstance) (A : List ℕ) : Bool :=
  x.sets.all fun s =>
    (s.any fun u => decide (u ∈ A)) &&
      (s.any fun v => decide (v ∈ x.ground) && decide (v ∉ A))

/-- Polynomial-time subset verifier for `SetSplitting`. -/
@[expose] def verifier : SetSplittingInstance × List Bool → Bool :=
  subsetVerifier SetSplittingInstance.ground (Function.uncurry check)

/-- Checking a candidate splitting subset is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_check :
    ComputableInPolyTime (Function.uncurry check) (encPair encSetSplitting (encList encNat))
      encBool := by
  unfold Function.uncurry check
  fun_prop

/-- The `SetSplitting` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encSetSplitting encBits) encBool :=
  computableInPolyTime_subsetVerifier (encγ := encNat) (by fun_prop) computableInPolyTime_check

/-- `SetSplitting.verifier` verifies `SetSplitting` with linear certificate length. -/
theorem isVerifier : IsVerifier encSetSplitting Polynomial.X verifier SetSplitting := by
  refine isVerifier_subsetVerifier (fun x => ?_) fun x l _ _ => ?_
  · rw [encSetSplitting_apply]
    have hle := length_le_length_encList encNat x.ground
    enc_len [Polynomial.eval_X]
  · simp only [Function.uncurry, check, List.all_eq_true, Bool.and_eq_true, List.any_eq_true,
      decide_eq_true_eq, List.mem_toFinset]

/-- **`SetSplitting` belongs to `NP`.** -/
theorem mem_NP : SetSplitting ∈ NP encSetSplitting :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end SetSplitting

namespace SetSplittingInstance

/-- Every element occurring in any subset of `x.sets` is declared in `x.ground`. -/
@[expose] def Valid (x : SetSplittingInstance) : Prop :=
  ∀ s ∈ x.sets, ∀ v ∈ s, v ∈ x.ground

/-- Executable check that every subset element lies in `x.ground`. -/
@[expose] def validBool (x : SetSplittingInstance) : Bool :=
  x.sets.all fun s => s.all fun v => decide (v ∈ x.ground)

/-- `validBool` decides `Valid`. -/
theorem validBool_eq_true_iff (x : SetSplittingInstance) : x.validBool = true ↔ x.Valid := by
  simp only [validBool, Valid, List.all_eq_true, decide_eq_true_eq]

/-- Checking `validBool` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_validBool :
    ComputableInPolyTime validBool encSetSplitting encBool := by
  unfold validBool
  fun_prop

/-- Executable guard checking `x.Valid` together with uniform subset size `≤ k`. -/
@[expose] def maxSetSizeBool (k : ℕ) (x : SetSplittingInstance) : Bool :=
  x.validBool && x.sets.all fun s => decide (s.length ≤ k)

/-- `maxSetSizeBool k` decides `x.Valid ∧ ∀ s ∈ x.sets, s.length ≤ k`. -/
theorem maxSetSizeBool_eq_true_iff (k : ℕ) (x : SetSplittingInstance) :
    x.maxSetSizeBool k = true ↔ x.Valid ∧ ∀ s ∈ x.sets, s.length ≤ k := by
  simp only [maxSetSizeBool, Bool.and_eq_true, validBool_eq_true_iff, List.all_eq_true,
    decide_eq_true_eq]

/-- Checking `maxSetSizeBool k` is polynomial-time for each fixed `k`. -/
@[fun_prop]
theorem computableInPolyTime_maxSetSizeBool (k : ℕ) :
    ComputableInPolyTime (maxSetSizeBool k) encSetSplitting encBool := by
  unfold maxSetSizeBool
  fun_prop

/-- Number of ordered splitting bipartitions `(A, B)` of `x.ground.toFinset`. -/
@[expose] noncomputable def count (x : SetSplittingInstance) : ℕ :=
  Nat.card {P : Finset ℕ × Finset ℕ //
    P.1 ∪ P.2 = x.ground.toFinset ∧ Disjoint P.1 P.2 ∧
      ∀ s ∈ x.sets, (∃ a ∈ s, a ∈ P.1) ∧ (∃ b ∈ s, b ∈ P.2)}

/-- The duplicate-free ground list preserving first occurrences. -/
@[expose] def distinctGround (x : SetSplittingInstance) : List ℕ :=
  selectDistinct x.ground (List.replicate x.ground.length true)

theorem mem_distinctGround {x : SetSplittingInstance} {v : ℕ} :
    v ∈ x.distinctGround ↔ v ∈ x.ground :=
  mem_selectDistinct_replicate

theorem nodup_distinctGround (x : SetSplittingInstance) : x.distinctGround.Nodup :=
  nodup_selectDistinct _ _

theorem length_distinctGround (x : SetSplittingInstance) :
    x.distinctGround.length = x.ground.toFinset.card :=
  length_selectDistinct_replicate x.ground

theorem length_distinctGround_le_enc (x : SetSplittingInstance) :
    x.distinctGround.length ≤ (encSetSplitting x).length := by
  rw [length_distinctGround]
  refine x.ground.toFinset_card_le.trans ?_
  have hle := length_le_length_encList encNat x.ground
  rw [encSetSplitting_apply]
  enc_len

@[fun_prop]
theorem computableInPolyTime_distinctGround :
    ComputableInPolyTime distinctGround encSetSplitting (encList encNat) := by
  unfold distinctGround
  fun_prop

/-- Set-splitting CNF formula on the original variable names `ℕ`. -/
@[expose] def toCNF (x : SetSplittingInstance) : CNF ℕ :=
  CNF.setSplittingCNF x.sets

/-- Dense declared-variable CNF compilation on `n = |ground.toFinset|` variables. -/
@[expose] def toDeclaredCNF (x : SetSplittingInstance) : ℕ × CNF ℕ :=
  (x.distinctGround.length, x.toCNF.relabel x.distinctGround.idxOf)

/-- Every clause of `x.toCNF` has length at most `k` when every set in `x.sets` has length at most
`k`. -/
theorem length_le_of_mem_toCNF {k : ℕ} {x : SetSplittingInstance}
    (hk : ∀ s ∈ x.sets, s.length ≤ k) {c : Clause ℕ} (hc : c ∈ x.toCNF) :
    c.length ≤ k := by
  simp only [toCNF, CNF.setSplittingCNF, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨s, hs, rfl | rfl⟩ := hc <;> simp only [List.length_map] <;> exact hk s hs

/-- Every clause of `(x.toDeclaredCNF).2` has length at most `k` when every set has length at most
`k`. -/
theorem length_le_of_mem_toDeclaredCNF {k : ℕ} {x : SetSplittingInstance}
    (hk : ∀ s ∈ x.sets, s.length ≤ k) {c : Clause ℕ} (hc : c ∈ (x.toDeclaredCNF).2) :
    c.length ≤ k := by
  simp only [toDeclaredCNF, CNF.relabel, Clause.relabel, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  rw [List.length_map]
  exact length_le_of_mem_toCNF hk hc₀

/-- Every occurring variable of `x.toCNF` belongs to `x.ground.toFinset` when `x.Valid`. -/
theorem vars_toCNF_subset {x : SetSplittingInstance} (hx : x.Valid) :
    x.toCNF.vars.toFinset ⊆ x.ground.toFinset := by
  intro v hv
  rw [List.mem_toFinset, toCNF, CNF.vars, List.mem_map] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  rw [List.mem_flatten] at hl
  obtain ⟨c, hc, hl⟩ := hl
  simp only [CNF.setSplittingCNF, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨s, hs, rfl | rfl⟩ := hc <;>
    obtain ⟨u, hu, hlu⟩ := List.mem_map.mp hl <;>
    cases hlu <;>
    exact List.mem_toFinset.mpr (hx s hs _ hu)

/-- Variable count of `x.toCNF` is at most `|x.ground.toFinset|` when `x.Valid`. -/
theorem numVars_toCNF_le {x : SetSplittingInstance} (hx : x.Valid) :
    x.toCNF.numVars ≤ x.ground.toFinset.card :=
  Finset.card_le_card (vars_toCNF_subset hx)

/-- `x.toCNF` has exactly `2 * x.sets.length` clauses. -/
theorem length_toCNF (x : SetSplittingInstance) : x.toCNF.length = 2 * x.sets.length := by
  simp [toCNF, CNF.setSplittingCNF, List.length_flatMap, List.map_const', List.sum_replicate,
    smul_eq_mul, Nat.mul_comm]

/-- Explicit assignment bijection between models of `x.toCNF` on `x.ground.toFinset` and
ordered splitting bipartitions of `x.ground.toFinset`. -/
def toCNFEquiv {x : SetSplittingInstance} (hx : x.Valid) :
    {σ : x.ground.toFinset → Bool //
      x.toCNF.eval (fun v => if hv : v ∈ x.ground.toFinset then σ ⟨v, hv⟩ else false) = true} ≃
      {P : Finset ℕ × Finset ℕ //
        P.1 ∪ P.2 = x.ground.toFinset ∧ Disjoint P.1 P.2 ∧
          ∀ s ∈ x.sets, (∃ a ∈ s, a ∈ P.1) ∧ (∃ b ∈ s, b ∈ P.2)} :=
  CNF.setSplittingCNFEquiv x.ground.toFinset x.sets
    fun s hs v hv => List.mem_toFinset.mpr (hx s hs v hv)

/-- **Exact model count of `x.toCNF` on `x.ground.toFinset` equals `x.count`.** -/
theorem modelCountOn_toCNF {x : SetSplittingInstance} (hx : x.Valid) :
    x.toCNF.modelCountOn x.ground.toFinset = x.count :=
  CNF.modelCountOn_setSplittingCNF x.ground.toFinset x.sets
    fun s hs v hv => List.mem_toFinset.mpr (hx s hs v hv)

/-- Under `x.Valid`, `idxOf` maps every occurring variable of `x.toCNF` into
`Finset.range x.distinctGround.length`. -/
theorem vars_toDeclaredCNF_subset {x : SetSplittingInstance} (hx : x.Valid) :
    (x.toDeclaredCNF).2.vars.toFinset ⊆ Finset.range x.distinctGround.length := by
  intro i hi
  rw [toDeclaredCNF, List.mem_toFinset, CNF.vars_relabel, List.mem_map] at hi
  obtain ⟨v, hv, rfl⟩ := hi
  have hvU : v ∈ x.distinctGround :=
    mem_distinctGround.mpr
      (List.mem_toFinset.mp (vars_toCNF_subset hx (List.mem_toFinset.mpr hv)))
  exact Finset.mem_range.mpr (List.idxOf_lt_length_iff.mpr hvU)

theorem validDeclaredInput_toDeclaredCNF {k : ℕ} {x : SetSplittingInstance}
    (hx : x.maxSetSizeBool k = true) :
    CNF.validDeclaredInput k (x.toDeclaredCNF).1 (x.toDeclaredCNF).2 = true := by
  obtain ⟨hval, hk⟩ := (maxSetSizeBool_eq_true_iff k x).mp hx
  exact CNF.validDeclaredInput_eq_true_iff.mpr
    ⟨fun _ hc => length_le_of_mem_toDeclaredCNF hk hc, vars_toDeclaredCNF_subset hval⟩

/-- **Exact model count of `x.toDeclaredCNF` on `Finset.range |U|` equals `x.count`.** -/
theorem modelCountOn_toDeclaredCNF {x : SetSplittingInstance} (hx : x.Valid) :
    (x.toDeclaredCNF).2.modelCountOn (Finset.range (x.toDeclaredCNF).1) = x.count := by
  have hinj : Set.InjOn x.distinctGround.idxOf {v | v ∈ x.toCNF.vars} := by
    intro u hu v hv huv
    have hu' : u ∈ x.distinctGround :=
      mem_distinctGround.mpr
        (List.mem_toFinset.mp (vars_toCNF_subset hx (List.mem_toFinset.mpr hu)))
    exact (List.idxOf_inj hu').mp huv
  have hnum : (x.toDeclaredCNF).2.numVars = x.toCNF.numVars := by
    rw [CNF.numVars, toDeclaredCNF, CNF.vars_relabel]
    have hmap : (x.toCNF.vars.map x.distinctGround.idxOf).toFinset =
        x.toCNF.vars.toFinset.image x.distinctGround.idxOf := by
      ext i
      simp
    rw [hmap]
    exact Finset.card_image_of_injOn fun u hu v hv h =>
      hinj (List.mem_toFinset.mp hu) (List.mem_toFinset.mp hv) h
  have hmc : (x.toDeclaredCNF).2.modelCount = x.toCNF.modelCount :=
    CNF.modelCount_relabel_of_injOn x.toCNF hinj
  have hdecl : (x.toDeclaredCNF).1 = x.distinctGround.length := rfl
  rw [hdecl, CNF.modelCountOn_eq_mul_modelCount _ _ (vars_toDeclaredCNF_subset hx),
    Finset.card_range, hnum, hmc, length_distinctGround,
    ← CNF.modelCountOn_eq_mul_modelCount x.toCNF x.ground.toFinset (vars_toCNF_subset hx),
    modelCountOn_toCNF hx]

/-- Compiling `x` to `x.toCNF` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toCNF :
    ComputableInPolyTime toCNF encSetSplitting encCNF := by
  unfold toCNF CNF.setSplittingCNF
  fun_prop

/-- Compiling `x` to `(x.distinctGround.length, x.toDeclaredCNF.2)` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toDeclaredCNF :
    ComputableInPolyTime toDeclaredCNF encSetSplitting (encPair encUnary encCNF) := by
  have hlen : ComputableInPolyTime (fun x : SetSplittingInstance => x.distinctGround.length)
      encSetSplitting encUnary :=
    (ComputableTidilyInPolyTime.length encNat).computableInPolyTime.comp
      computableInPolyTime_distinctGround
  have hvar : ComputableTidilyInPolyTime
      (fun p : SetSplittingInstance × ℕ => p.1.distinctGround.idxOf p.2)
      (encPair encSetSplitting encNat) encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.idxOfWithInput
        (computableInPolyTime_distinctGround.comp (ComputableInPolyTime.fst _ _)).tidy
        (ComputableTidilyInPolyTime.snd _ _))
  have hlit : ComputableTidilyInPolyTime
      (fun p : (SetSplittingInstance × Clause ℕ) × Literal ℕ =>
        (p.1.1.distinctGround.idxOf p.2.1, p.2.2))
      (encPair (encPair encSetSplitting (encClause encNat)) (encPair encNat encBool))
      (encPair encNat encBool) := by
    have hv : ComputableTidilyInPolyTime
        (fun p : (SetSplittingInstance × Clause ℕ) × Literal ℕ =>
          p.1.1.distinctGround.idxOf p.2.1)
        (encPair (encPair encSetSplitting (encClause encNat)) (encPair encNat encBool)) encNat :=
      hvar.comp
        (((ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.fst _ _)).prod
          ((ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _)))
    fun_prop
  have hclause : ComputableTidilyInPolyTime
      (fun p : SetSplittingInstance × Clause ℕ =>
        p.2.map fun l => (p.1.distinctGround.idxOf l.1, l.2))
      (encPair encSetSplitting (encClause encNat)) (encClause encNat) :=
    ComputableTidilyInPolyTime.mapWithInput (ComputableTidilyInPolyTime.snd _ _) hlit
  have hcnf : ComputableInPolyTime
      (fun x : SetSplittingInstance => x.toCNF.relabel x.distinctGround.idxOf)
      encSetSplitting encCNF := by
    unfold CNF.relabel Clause.relabel Prod.map
    exact (ComputableTidilyInPolyTime.mapWithInput
      computableInPolyTime_toCNF.tidy hclause).computableInPolyTime
  exact hlen.prod hcnf

end SetSplittingInstance

end Cslib.Complexity
