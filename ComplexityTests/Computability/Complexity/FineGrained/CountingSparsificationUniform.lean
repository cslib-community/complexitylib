/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.FineGrained.CountingSparsificationUniform
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-! Concrete captured-context, normalization and independent-workspace controls.
The probe is deliberately not a general model counter: the two-unit control below detects that.
-/

open Cslib Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM
open Cslib.Complexity Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.CountingSparsify

@[expose] public section

namespace CountingSparsificationUniformTests

private abbrev Context := Bool × ℕ
private abbrev encContext : Context ↪ List Bool := encPair encBool encUnary
private abbrev encInput := encPair encContext encCNF

/-- A declared-count diagnostic for an empty or unit formula, selected by the runtime context. -/
def declaredProbe (x : (Bool × ℕ) × CNF ℕ) : ℕ :=
  if x.1.1 then 2 ^ (x.1.2 - if x.2.isEmpty then 0 else 1) else 0

private def unitFormula : CNF ℕ := [[(0, true)]]
private def twoUnits : CNF ℕ := [[(0, true)], [(1, true)]]
private def MOf (_ : Context) : ℕ := countingThresholdBase 2 1
private def BOf (_ : Context) : ℕ := 1

example : declaredProbe ((true, 3), unitFormula) = 4 := by decide
example : normalizeDeclaredLeaf Prod.snd declaredProbe ((true, 3), unitFormula) = 1 := by decide
example : normalizeDeclaredLeaf Prod.snd declaredProbe ((false, 3), unitFormula) = 0 := by decide

example : searchDeclaredWith Prod.snd MOf BOf 2 2 declaredProbe (true, 3) unitFormula = 8 := by
  decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 3) unitFormula = 4 := by decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (false, 3) unitFormula = 0 := by decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 1) unitFormula = 1 := by decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 0) [] = 1 := by decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 3) [] = 8 := by decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 3) [[]] = 0 := by decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 3) [[(0, true), (0, false)]] = 8 := by
  decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 1) [[(1, true)]] = 0 := by decide
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 3)
    [[(0, true), (1, true), (2, true)]] = 0 := by decide

-- The probe is not a model counter for arbitrary formulas: two independent units have one model.
example : searchDeclaredWith Prod.snd MOf BOf 2 2
    (normalizeDeclaredLeaf Prod.snd declaredProbe) (true, 2) twoUnits = 2 := by decide
example : ([(false, false), (false, true), (true, false), (true, true)].filter
    (fun a => twoUnits.eval fun v => if v = 0 then a.1 else a.2)).length = 1 := by decide

-- The same runtime binary clock routine sees different divisors, retaining its binary output.
example : rounds 1 twoUnits = 16 ∧ rounds 2 twoUnits = 8 ∧
    (encNat (rounds 1 twoUnits)).length = 5 := by decide
example : rounds 0 ([] : CNF ℕ) = 4 := by decide
example (payload : Bool) (N : ℕ) (φ : CNF ℕ) :
    (encInput ((payload, N), φ)).length = 2 * N + 7 + (encCNF φ).length := by
  simp only [encInput, encContext, length_encPair, encUnary_apply, List.length_replicate,
    encBool_apply, List.length_singleton]
  omega

example (payload : Bool) (N : ℕ) (φ : CNF ℕ) :
    (encPair encBool (encPair encUnary encCNF) (payload, N, φ)).length =
      2 * N + 4 + (encCNF φ).length := by
  simp only [length_encPair, encUnary_apply, List.length_replicate,
    encBool_apply, List.length_singleton]
  omega

private theorem declaredProbe_poly : ComputableInPolyTime declaredProbe encInput encNat := by
  unfold declaredProbe encInput encContext encCNF
  fun_prop

-- One total diagnostic machine is given an exponential time allowance and polynomial workspace.
-- Normalization still charges the intermediate declared-count output in its workspace.
example : ∃ d e, ComputableInO (normalizeDeclaredLeaf Prod.snd declaredProbe) encInput encNat
      (fun x => 2 ^ x.1.2 * ((encInput x).length + 1) ^ d +
        ((encInput x).length + (encNat (declaredProbe x)).length + 1) ^ e)
      (fun x => ((encInput x).length + 1) ^ d +
        ((encInput x).length + (encNat (declaredProbe x)).length + 1) ^ e) ∧
    PolyBounded (fun x : Context × CNF ℕ => (encInput x).length)
      (fun x => ((encInput x).length + 1) ^ d +
        ((encInput x).length + (encNat (declaredProbe x)).length + 1) ^ e) := by
  obtain ⟨d, _, hd⟩ := declaredProbe_poly.tidy.exists_degree
  have hh := (ComputableInO.of_tidy hd.inO).mono_le
    (T' := fun x => 2 ^ x.1.2 * ((encInput x).length + 1) ^ d)
    (fun x => by
      simpa only [one_mul] using Nat.mul_le_mul_right (((encInput x).length + 1) ^ d)
        (Nat.one_le_two_pow (n := x.1.2))) (fun _ => le_rfl)
  obtain ⟨e, he⟩ := exists_computableInO_normalizeDeclaredLeaf
    (show ComputableInPolyTime (Prod.snd : Context → ℕ) encContext encUnary
      by fun_prop) hh
  refine ⟨d, e, he, ?_⟩
  exact (polyBounded_pow (PolyBounded.self.add (.const 1)) d).add
    (polyBounded_pow
      ((PolyBounded.self.add declaredProbe_poly.polyBounded_length).add (.const 1)) e)

private def varyingB (p : Context) : ℕ := if p.1 then 1 else 2
private def varyingM (p : Context) : ℕ := countingThresholdBase 2 (varyingB p)

private theorem varying_depth (p : Context) : countingDepthCoeff 2 (varyingM p) = 4 := by
  simp [countingDepthCoeff]

private theorem varying_leaf_input_bound (g : Context × CNF ℕ → ℕ)
    (x : Bool × ℕ × CNF ℕ) (i : ℕ)
    (hc : let p := (x.1, x.2.1)
      let st := (step (varyingM p) 2 (fun ψ => g (p, ψ)))^[i] (init 2 x.2.2)
      st.2.1.isEmpty = false ∧
        isSparse (countingThreshold (varyingM p)) 2 (st.2.1.headD []) = true) :
    let p := (x.1, x.2.1)
    let st := (step (varyingM p) 2 (fun ψ => g (p, ψ)))^[i] (init 2 x.2.2)
    (encInput ((x.1, x.2.1), st.2.1.headD [])).length + 1 ≤
      2 * (encContext (x.1, x.2.1)).length + 2 + nodeBound 2 4 x.2.2 := by
  have hB : 1 ≤ varyingB (x.1, x.2.1) := by unfold varyingB; split <;> omega
  have hM2 := two_le_countingThresholdBase 2 (varyingB (x.1, x.2.1))
  have hTB := countingTreeBound_countingThresholdBase (by decide : 1 ≤ 2) hB
  have hp := (iterate_step_prefix_bounds (by omega) (by decide : 1 ≤ 2) hM2
    (by decide : 2 ≤ 2) hTB (fun ψ => g ((x.1, x.2.1), ψ)) x.2.2 i).2.2.2 hc
  have hlen := hp.2.2.2.2
  rw [show countingDepthCoeff 2 (countingThresholdBase 2 (varyingB (x.1, x.2.1))) = 4 from
    varying_depth (x.1, x.2.1)] at hlen
  dsimp only
  simp only [encInput, varyingM, length_encPair]
  omega

private theorem varying_leaf_allowance_poly (d : ℕ) :
    PolyBounded
      (fun x : Bool × ℕ × CNF ℕ => (encPair encBool (encPair encUnary encCNF) x).length)
      (fun x => (2 * (encContext (x.1, x.2.1)).length + 2 + nodeBound 2 4 x.2.2) ^ d) := by
  have hcontext : ComputableInPolyTime (fun x : Bool × ℕ × CNF ℕ => (x.1, x.2.1))
      (encPair encBool (encPair encUnary encCNF)) encContext := by
    unfold encContext
    fun_prop
  have hformula : ComputableInPolyTime (fun x : Bool × ℕ × CNF ℕ => x.2.2)
      (encPair encBool (encPair encUnary encCNF)) encCNF := by fun_prop
  exact polyBounded_pow
    ((((PolyBounded.const 2).mul hcontext.polyBounded_length).add (.const 2)).add
      ((polyBounded_nodeBound 2 4).comp hformula.polyBounded_length)) d

end CountingSparsificationUniformTests
