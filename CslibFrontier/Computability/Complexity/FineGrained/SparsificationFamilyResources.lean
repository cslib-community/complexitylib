/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.SparsificationFamily
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-!
# Separating sparse branching work from collected output

Branching computations depend only on the pending stack. The polynomial for those computations
must not be applied to the accumulated output, whose encoded size is charged linearly instead.

## Main results

* `Cslib.Complexity.Sparsify.Family.prefix_stack`: pending-stack and head wire bounds at every
  round.
* `Cslib.Complexity.Sparsify.Family.prefix_output`: accumulated-output wire bound at every round.
* `Cslib.Complexity.Sparsify.Family.step_split`: polynomial stack work and linear state copying.
* `Cslib.Complexity.Sparsify.Family.collect_quadratic_rounds`: the actual collector has a fixed
  quadratic round factor, with a polynomial only in the original encoded formula.
-/

public section
namespace Cslib.Complexity.Sparsify.Family
open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open Cslib.Logic.PL.CNF.Sparsification
open ClauseSet.Sparsification (threshold)

/-- The pending stack and its head remain polynomially sized, independently of collected output. -/
theorem prefix_stack {K α k M : ℕ} (hK : 1 ≤ K) (hα : 1 ≤ α) (hkK : k ≤ K)
    (hM : LeafBound K α M) (φ : CNF ℕ) (i : ℕ) :
    let st := (step K α)^[i] ([root k φ], [])
    (encList encCNF st.1).length ≤ stateBound K α φ ∧
      (encCNF (st.1.headD [])).length ≤ nodeBound K α φ := by
  obtain ⟨stk, acc, heq, hstk, hmem⟩ :=
    (Sparsify.iterate_step hK hα hkK hM (fun _ => false) φ).2 i
  have hi := congrArg Prod.fst (iterate_any K α (fun _ => false) i ([root k φ], []))
  change ((step K α)^[i] ([root k φ], [])).1 =
    ((Sparsify.step K α (fun _ => false))^[i] ([root k φ], false)).1 at hi
  rw [heq] at hi
  change ((step K α)^[i] ([root k φ], [])).1 = stk.map Subtype.val at hi
  dsimp only
  rw [hi]
  constructor
  · have hb := length_encState_le hK hα hkK hstk hmem (acc := acc)
    simp only [Sparsify.encState, length_encPair, encBool_apply, List.length_singleton] at hb
    omega
  · cases stk with
    | nil => exact Nat.zero_le _
    | cons s rest =>
      obtain ⟨w, hw, rfl⟩ := hmem s List.mem_cons_self
      exact length_encCNF_walk_le hK hα hkK hw

/-- Each round emits at most one reached formula; the actual framed accumulator wire is charged. -/
theorem prefix_output {K α k M : ℕ} (hK : 1 ≤ K) (hα : 1 ≤ α) (hkK : k ≤ K)
    (hM : LeafBound K α M) (φ : CNF ℕ) (i : ℕ) :
    (encList encCNF ((step K α)^[i] ([root k φ], [])).2).length ≤
      i * (2 * nodeBound K α φ + 1) := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hh := (prefix_stack hK hα hkK hM φ i).2
    rw [Function.iterate_succ_apply']
    simp only [step]
    split_ifs
    · nlinarith
    · simp only [encList_cons, List.length_append, length_frame]
      nlinarith
    · nlinarith

/-- Polynomial branching sees only the stack; copying the entire state is charged linearly. -/
theorem step_split (K α : ℕ) :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO (step K α) encCollectorState encCollectorState
        (fun s => P (encList encCNF s.1).length + (encCollectorState s).length)
        (fun s => P (encList encCNF s.1).length + (encCollectorState s).length) := by
  let e := encList encCNF
  have hs := computableInPolyTime_isSparse encNat
    (ClauseSet.Sparsification.computableInPolyTime_threshold_le K α) K
  have hn := computableInPolyTime_next encNat
    (ClauseSet.Sparsification.computableInPolyTime_threshold_le K α) K
  have he : ComputableInPolyTime (List.isEmpty : List (CNF ℕ) → Bool) e encBool := by
    dsimp only [e]; fun_prop
  have hc : ComputableInPolyTime
      (fun stk : List (CNF ℕ) => isSparse (threshold K α) K (stk.headD [])) e encBool := by
    dsimp only [e]; fun_prop
  have hi : ComputableInPolyTime (fun stk : List (CNF ℕ) =>
      next (threshold K α) K (stk.headD []) false ::
        next (threshold K α) K (stk.headD []) true :: stk.tail) e e := by
    dsimp only [e, encCNF]; fun_prop
  obtain ⟨de, ee, he⟩ := he.exists_degree
  obtain ⟨dc, ec, hc⟩ := hc.exists_degree
  obtain ⟨di, ei, hi⟩ := hi.exists_degree
  let d := de + dc + di
  have he' := ((he.mono (d' := d) (e' := ee) (by omega) le_rfl).inO).comp
    (ComputableInO.fst e e)
  have hc' := ((hc.mono (d' := d) (e' := ec) (by omega) le_rfl).inO).comp
    (ComputableInO.fst e e)
  have hi' := (((hi.mono (d' := d) (e' := ei) (by omega) le_rfl).inO).comp
    (ComputableInO.fst e e)).prod (ComputableInO.snd e e)
  have hh := (ComputableInO.headD' (enc := encCNF) []).comp_linear
    (ComputableInO.fst e e)
  have ht := (ComputableInO.tail' (enc := encCNF)).comp_linear (ComputableInO.fst e e)
  have hl := ht.prod ((ComputableInO.cons' (enc := encCNF)).comp_linear
    (hh.prod (ComputableInO.snd e e)))
  have h := he'.ite (ComputableInO.of_eq (encIn := encCollectorState)
    (encMid := encCollectorState) fun _ => rfl) (hc'.ite hl hi')
  refine ⟨fun n => (n + 1) ^ d, by fun_prop,
    fun _ _ hab => Nat.pow_le_pow_left (by omega) d, ?_⟩
  refine (h.mono 8 (fun s => ?_) (fun s => ?_)).of_enc_eq (fun _ => rfl)
  all_goals
    dsimp only [Function.comp_apply, e, encCollectorState]
    split_ifs <;> omega

/-- The node wire bound is polynomial in the original encoded formula, not in the output list. -/
theorem nodeBound_poly (K α : ℕ) :
    PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (nodeBound K α) := by
  have hv : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) CNF.numVars :=
    PolyBounded.self.mono fun φ => φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
  have hl : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (List.length : CNF ℕ → ℕ) :=
    PolyBounded.self.mono fun φ => length_le_length_encList _ φ
  unfold nodeBound
  with_reducible growth_poly

/-- The pending-stack wire bound is polynomial in the original encoded formula. -/
theorem stateBound_poly (K α : ℕ) :
    PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (stateBound K α) := by
  have hv : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) CNF.numVars :=
    PolyBounded.self.mono fun φ => φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
  have hn := nodeBound_poly K α
  unfold stateBound
  with_reducible growth_poly

/-- A native collector with a quadratic round factor and a polynomial in the original input wire.
The exponent of the round factor is fixed before the threshold parameter is selected. -/
theorem collect_quadratic_rounds {K α k M : ℕ} (hK : 1 ≤ K) (hα : 1 ≤ α)
    (hkK : k ≤ K) (hM : LeafBound K α M) :
    ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
      ComputableInO (collect K α k M) encCNF (encList encCNF)
        (fun φ => (rounds M φ + 1) ^ 2 * Q (encCNF φ).length)
        (fun φ => (rounds M φ + 1) ^ 2 * Q (encCNF φ).length) := by
  obtain ⟨P, hp, hm, hs⟩ := step_split K α
  obtain ⟨dn, en, hn⟩ := (computableInPolyTime_rounds M).exists_degree
  obtain ⟨di, ei, hi⟩ := (init_polyTime k).exists_degree
  let b := fun φ : CNF ℕ =>
    2 * stateBound K α φ + 1 + rounds M φ * (2 * nodeBound K α φ + 1)
  have hstate (φ : CNF ℕ) (i : ℕ) (hi : i ≤ rounds M φ) :
      (encCollectorState ((step K α)^[i] ([root k φ], []))).length ≤ b φ := by
    have hstk := (prefix_stack hK hα hkK hM φ i).1
    have hout := (prefix_output hK hα hkK hM φ i).trans
      (Nat.mul_le_mul_right _ hi)
    simp only [encCollectorState, length_encPair, b]
    omega
  have hround (φ : CNF ℕ) (i : ℕ) (hi : i ≤ rounds M φ) :
      P (encList encCNF ((step K α)^[i] ([root k φ], [])).1).length +
          (encCollectorState ((step K α)^[i] ([root k φ], []))).length ≤
        P (stateBound K α φ) + b φ :=
    Nat.add_le_add (hm (prefix_stack hK hα hkK hM φ i).1) (hstate φ i hi)
  have machine := (ComputableInO.iterate hn.inO hi.inO hs hround hround hstate).snd'
  let size := fun φ : CNF ℕ => (encCNF φ).length
  have hnode : PolyBounded size (nodeBound K α) := nodeBound_poly K α
  have hstack : PolyBounded size (stateBound K α) := stateBound_poly K α
  have hpoly : PolyBounded size (fun φ => P (stateBound K α φ)) :=
    (PolyBounded.of_polynomiallyBounded id hp).comp hstack
  have hcounter : PolyBounded size (fun φ => (encNat (rounds M φ)).length) :=
    (PolyBounded.self.add (.const 3)).mono fun φ => by
      dsimp only [size]
      rw [length_encNat_rounds]
      have hN := φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
      have hd := Nat.div_le_self φ.numVars M
      omega
  let u := fun φ : CNF ℕ => (size φ + 1) ^ dn + (size φ + 1) ^ di +
    P (stateBound K α φ) + stateBound K α φ + nodeBound K α φ +
      ((encNat (rounds M φ)).length + 1) ^ 2 + 1
  have hu : PolyBounded size u := by
    dsimp only [u]
    growth_poly
  obtain ⟨Q, hQ, hmQ, hle⟩ := exists_mono_poly hu
  refine ⟨Q, hQ, hmQ, machine.mono 20 (fun φ => ?_) (fun φ => ?_)⟩ <;>
  · have h := hle φ
    have hB : b φ ≤ 3 * (rounds M φ + 1) * Q (size φ) := by
      have hc : 2 * nodeBound K α φ + 1 ≤ 3 * Q (size φ) := by
        dsimp only [u] at h
        omega
      have hm := Nat.mul_le_mul_left (rounds M φ) hc
      have hc0 : 2 * stateBound K α φ + 1 ≤ 3 * Q (size φ) := by
        dsimp only [u] at h
        omega
      calc b φ ≤ 3 * Q (size φ) + rounds M φ * (3 * Q (size φ)) :=
            Nat.add_le_add hc0 hm
        _ = 3 * (rounds M φ + 1) * Q (size φ) := by ring
    have hr : 1 ≤ rounds M φ + 1 := by omega
    have hq : 1 ≤ Q (size φ) := by dsimp only [u] at h; omega
    have hsetup : (size φ + 1) ^ dn + (size φ + 1) ^ di ≤ Q (size φ) := by
      dsimp only [u] at h
      omega
    have hwork : P (stateBound K α φ) + ((encNat (rounds M φ)).length + 1) ^ 2 ≤
        Q (size φ) := by
      dsimp only [u] at h
      omega
    have hmul := Nat.mul_le_mul_left (rounds M φ + 1)
      (Nat.add_le_add hwork (Nat.mul_le_mul_left 2 hB))
    have hrq := Nat.mul_le_mul_right (Q (size φ)) hr
    dsimp only [size] at *
    have hsq : Q (encCNF φ).length ≤ (rounds M φ + 1) ^ 2 * Q (encCNF φ).length :=
      Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)
    nlinarith [Nat.le_mul_self (rounds M φ + 1)]

end Cslib.Complexity.Sparsify.Family
