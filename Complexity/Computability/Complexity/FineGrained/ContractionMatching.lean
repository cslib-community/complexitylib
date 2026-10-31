/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.ContractionPartitionFunction
public import Complexity.Logics.Propositional.CSP.Permanent
public import Complexity.Computability.Complexity.Problems.Graph.PerfectMatching
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Preprocess
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Foundations.Data.List.OfFn
import Complexity.Foundations.Data.Nat.SqrtLog.Shifted
import Mathlib.Data.List.GetD

/-!
# Permanents and perfect matchings of bounded degree by tensor contraction
-/

public section

namespace Cslib.Complexity.ContractionMatching

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### Exactly-one instances in which every variable occurs at most twice -/

/-- The instance answered in place of an instance with an empty or overlong scope: one
exactly-one constraint on a repeated variable, whose partition function is zero. -/
@[expose] def zeroInstance : CSP Unit ℕ := [((), [0, 0])]

/-- The instance handed to the counter: `F` itself when each of its constraints has between one
and `d` variables, and `zeroInstance` otherwise. -/
@[expose] def guarded (d : ℕ) (F : CSP Unit ℕ) : CSP Unit ℕ :=
  if F.all fun c => decide (1 ≤ c.2.length ∧ c.2.length ≤ d) then F else zeroInstance

theorem partitionFunction_zeroInstance :
    zeroInstance.partitionFunction CSP.exactlyOneWeight = 0 := by
  decide

/-- **Guarding preserves the partition function** of an instance whose constraints have at most
`d` variables: if one of them has none, both partition functions are zero. -/
theorem partitionFunction_guarded {d : ℕ} {F : CSP Unit ℕ} (hF : ∀ c ∈ F, c.2.length ≤ d) :
    (guarded d F).partitionFunction CSP.exactlyOneWeight =
      F.partitionFunction CSP.exactlyOneWeight := by
  unfold guarded
  split_ifs with hg
  · rfl
  · rw [partitionFunction_zeroInstance]
    simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at hg
    obtain ⟨c, hc, hlen⟩ := hg
    have h0 : c.2 = [] := List.eq_nil_of_length_eq_zero (by have := hF c hc; omega)
    refine (CSP.partitionFunction_eq_zero_of_mem hc fun w hw => ?_).symm
    rw [h0, List.length_nil, List.length_eq_zero_iff] at hw
    rw [hw]
    rfl

private theorem length_mem_guarded {d : ℕ} {F : CSP Unit ℕ} {c : Constraint Unit ℕ}
    (hc : c ∈ guarded d F) : 1 ≤ c.2.length ∧ c.2.length ≤ d + 2 := by
  unfold guarded at hc
  split_ifs at hc with hg
  · simp only [List.all_eq_true, decide_eq_true_eq] at hg
    have := hg c hc
    omega
  · simp only [zeroInstance, List.mem_singleton] at hc
    subst hc
    simp

private theorem count_vars_guarded {d : ℕ} {F : CSP Unit ℕ} (hF : ∀ v, F.vars.count v ≤ 2)
    (v : ℕ) : (guarded d F).vars.count v ≤ 2 := by
  unfold guarded
  split_ifs
  · exact hF v
  · exact List.count_le_length.trans (by decide)

private theorem numVars_guarded_le (d : ℕ) (F : CSP Unit ℕ) :
    (guarded d F).numVars ≤ d * F.length + 1 := by
  unfold guarded
  split_ifs with hg
  · simp only [List.all_eq_true, decide_eq_true_eq] at hg
    refine (List.toFinset_card_le _).trans ?_
    rw [CSP.vars, List.length_flatMap]
    refine (List.sum_le_length_nsmul _ d fun x hx => ?_).trans ?_
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact (hg c hc).2
    · rw [List.length_map, smul_eq_mul, Nat.mul_comm]
      exact Nat.le_succ _
  · exact (show zeroInstance.numVars = 1 by decide).trans_le (Nat.le_add_left _ _)

/-- **Exactly-one counting on bounded-occurrence instances by tensor contraction.** Let `inst` be
a polynomial-time map to exactly-one instances in which every variable occurs at most twice and
whose number of constraints is at most `C * size a + C`. For each `d`, one machine computes the
partition function of `inst a` whenever its constraints have at most `d` variables. On every
input it runs in time `2 ^ (A (size a + 1) / √⌊log₂ (size a + 2)⌋)` times a polynomial in the
encoding length, and in polynomial space. The machine first replaces an instance with an empty or
overlong scope by `zeroInstance` (`guarded`), then runs the counter of
`ContractionPartitionFunction.exists_partitionFunctionCounter_of_finite`. -/
theorem exists_exactlyOneCounter {α : Type} {enc : α ↪ List Bool} (d C : ℕ)
    {inst : α → CSP Unit ℕ} {size : α → ℕ}
    (hinst : ComputableInPolyTime inst enc (encCSP encUnit encNat))
    (hocc : ∀ a v, (inst a).vars.count v ≤ 2) (hsize : ∀ a, (inst a).length ≤ C * size a + C) :
    ∃ (count : α → ℕ) (A e b : ℕ),
      (∀ a, (∀ c ∈ inst a, c.2.length ≤ d) →
        count a = (inst a).partitionFunction CSP.exactlyOneWeight) ∧
      ComputableInO count enc encNat
        (fun a => 2 ^ (A * (size a + 1) / Nat.sqrt (Nat.log 2 (size a + 2))) *
          ((enc a).length + 1) ^ e)
        (fun a => ((enc a).length + 1) ^ b) := by
  obtain ⟨count, T, S, e, b, hcount, hc, hS, hT⟩ :=
    ContractionPartitionFunction.exists_partitionFunctionCounter_of_finite encUnit (d + 2)
      CSP.exactlyOneWeight
  obtain ⟨A, hA⟩ := hT 2
  have hred : ComputableInPolyTime (fun a => guarded d (inst a)) enc (encCSP encUnit encNat) := by
    unfold guarded
    fun_prop
  obtain ⟨e', b', hO⟩ := hc.comp_polyTime hred
    (fun a => hA _ (count_vars_guarded (hocc a))) (fun a => (hS _).le)
  refine ⟨fun a => count (guarded d (inst a)), A * (8 * (d * C + 1) + 14), e', b',
    fun a ha => ?_, hO.mono_le (fun a => ?_) fun _ => le_rfl⟩
  · exact (hcount _ fun c hc => length_mem_guarded hc).trans (partitionFunction_guarded ha)
  · have hle : (guarded d (inst a)).numVars ≤ (d * C + 1) * size a + (d * C + 1) := by
      have h1 := numVars_guarded_le d (inst a)
      have h2 := Nat.mul_le_mul_left d (hsize a)
      nlinarith
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos
      (Nat.mul_succ_div_sqrt_log_two_le hle))

/-- Recoding the variables of a CSP instance from unary to binary is polynomial-time. -/
private theorem computableInPolyTime_unary_to_binary :
    ComputableInPolyTime (fun F : CSP Unit ℕ => F) (encCSP encUnit encUnary)
      (encCSP encUnit encNat) := by
  have h : ComputableInPolyTime (CSP.relabel (Rel := Unit) (V := ℕ) (W := ℕ) fun n => n)
      (encCSP encUnit encUnary) (encCSP encUnit encNat) := by
    unfold CSP.relabel Constraint.relabel
    fun_prop
  have heq : (CSP.relabel (Rel := Unit) (V := ℕ) (W := ℕ) fun n => n) = fun F => F := by
    funext F
    induction F with
    | nil => rfl
    | cons c F ih =>
      simp only [CSP.relabel, List.map_cons, Constraint.relabel, List.map_id']
      exact congrArg (c :: ·) ih
  rwa [heq] at h

/-! ### Permanents -/

/-- Entry `(i, j)` of the matrix with rows `rows`: entry `j` of row `i`, or `false` when it is
missing. -/
@[expose] def rowEntry (rows : List (List Bool)) (i j : ℕ) : Bool :=
  (rows.getD i []).getD j false

/-- The square `0/1` matrix with rows `rows`, of size `rows.length`: entry `(i, j)` is one when
entry `j` of row `i` is `true`, and zero when it is `false` or missing. -/
@[expose] def rowsMatrix (rows : List (List Bool)) :
    Matrix (Fin rows.length) (Fin rows.length) ℕ :=
  Matrix.of fun i j => if rows[i].getD j false then 1 else 0

theorem rowsMatrix_eq (rows : List (List Bool)) :
    rowsMatrix rows =
      Matrix.of fun i j : Fin rows.length => if rowEntry rows i j then 1 else 0 := by
  ext i j
  simp only [rowsMatrix, rowEntry, Matrix.of_apply, List.getD_eq_getElem _ _ i.2]
  rfl

/-- The nonzero entries of `rowsMatrix rows` are the `true` entries of the rows. -/
theorem rowsMatrix_ne_zero_iff {rows : List (List Bool)} {i j : Fin rows.length} :
    rowsMatrix rows i j ≠ 0 ↔ rowEntry rows i j = true := by
  rw [rowsMatrix_eq, Matrix.of_apply]
  cases rowEntry rows i j <;> simp

/-- Building the permanent instance of the matrix with rows `rows` is polynomial-time. -/
theorem computableInPolyTime_permanentInstance :
    ComputableInPolyTime (fun rows : List (List Bool) =>
        CSP.permanentInstance rows.length (rowEntry rows))
      (encList encBits) (encCSP encUnit encNat) := by
  refine computableInPolyTime_unary_to_binary.comp ?_
  unfold rowEntry
  fun_prop

open Finset in
/-- Under the degree promise, every constraint of the permanent instance has at most `d`
variables. -/
private theorem length_le_of_mem_permanentInstance {d : ℕ} {rows : List (List Bool)}
    (hrow : ∀ i, #{j | rowsMatrix rows i j ≠ 0} ≤ d)
    (hcol : ∀ j, #{i | rowsMatrix rows i j ≠ 0} ≤ d) {c : Constraint Unit ℕ}
    (hc : c ∈ CSP.permanentInstance rows.length (rowEntry rows)) : c.2.length ≤ d := by
  simp only [CSP.permanentInstance, List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [List.length_map, ← List.countP_eq_length_filter, List.countP_range_eq_card_filter]
    simpa only [rowsMatrix_ne_zero_iff] using hrow ⟨i, hi⟩
  · rw [List.length_map, ← List.countP_eq_length_filter, List.countP_range_eq_card_filter]
    simpa only [rowsMatrix_ne_zero_iff] using hcol ⟨j, hj⟩

open Finset in
/-- **The `0/1` permanent with at most `d` nonzero entries per row and column in time
`2 ^ O(n / √log n)`.** For each `d`, one machine reads a list of rows `rows` (encoded by
`encList encBits`) and, when every row and every column of the `n × n` matrix `rowsMatrix rows`
has at most `d` nonzero entries, outputs its permanent. On every input it runs in time
`2 ^ (A (n + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding length, and in polynomial
space, for `n = rows.length`. The constants `A`, `e` and `b` depend only on `d`. -/
theorem exists_permanentCounter (d : ℕ) :
    ∃ (count : List (List Bool) → ℕ) (A e b : ℕ),
      (∀ rows : List (List Bool), (∀ i, #{j | rowsMatrix rows i j ≠ 0} ≤ d) →
        (∀ j, #{i | rowsMatrix rows i j ≠ 0} ≤ d) → count rows = (rowsMatrix rows).permanent) ∧
      ComputableInO count (encList encBits) encNat
        (fun rows => 2 ^ (A * (rows.length + 1) / Nat.sqrt (Nat.log 2 (rows.length + 2))) *
          ((encList encBits rows).length + 1) ^ e)
        (fun rows => ((encList encBits rows).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_exactlyOneCounter d 2
    (size := fun rows : List (List Bool) => rows.length) computableInPolyTime_permanentInstance
    (fun rows => CSP.count_vars_permanentInstance _ _) fun rows => by
      simp only [CSP.permanentInstance, List.length_append, List.length_map, List.length_range]
      omega
  refine ⟨count, A, e, b, fun rows hrow hcol => ?_, hc⟩
  rw [hcount rows fun c hc => length_le_of_mem_permanentInstance hrow hcol hc,
    CSP.partitionFunction_permanentInstance, rowsMatrix_eq]

/-! ### Perfect matchings -/

/-- Listing the edges of `G.induced` is polynomial-time. -/
theorem computableInPolyTime_edgeList :
    ComputableInPolyTime Graph.edgeList encGraph (encList (encPair encNat encNat)) := by
  unfold Graph.edgeList encGraph
  fun_prop

/-- Building the perfect-matching instance of a graph is polynomial-time. -/
theorem computableInPolyTime_perfectMatchingInstance :
    ComputableInPolyTime Graph.perfectMatchingInstance encGraph (encCSP encUnit encNat) := by
  have hE := computableInPolyTime_edgeList
  refine computableInPolyTime_unary_to_binary.comp
    (?_ : ComputableInPolyTime (fun G : Graph => G.perfectMatchingInstance) _ _)
  unfold Graph.perfectMatchingInstance Graph.incident
  fun_prop

/-- **Perfect matchings of graphs of maximum degree `d` in time `2 ^ O(n / √log n)`.** For each
`d`, one machine reads a graph `G` (encoded by `encGraph`) and, when every vertex of `G.induced`
has at most `d` neighbours, outputs the number of perfect matchings of `G.induced`. On every
input it runs in time `2 ^ (A (n + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding
length, and in polynomial space, for `n` distinct declared vertices. The constants `A`, `e` and
`b` depend only on `d`. -/
theorem exists_perfectMatchingCounter (d : ℕ) :
    ∃ (count : Graph → ℕ) (A e b : ℕ),
      (∀ G : Graph, (∀ v, Nat.card (G.induced.neighborSet v) ≤ d) →
        count G = Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching}) ∧
      ComputableInO count encGraph encNat
        (fun G => 2 ^ (A * (G.1.toFinset.card + 1) / Nat.sqrt (Nat.log 2 (G.1.toFinset.card + 2))) *
          ((encGraph G).length + 1) ^ e)
        (fun G => ((encGraph G).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_exactlyOneCounter d 1
    (size := fun G : Graph => G.1.toFinset.card) computableInPolyTime_perfectMatchingInstance
    (fun G => Graph.count_vars_perfectMatchingInstance G) fun G => by
      rw [Graph.length_perfectMatchingInstance]
      omega
  refine ⟨count, A, e, b, fun G hdeg => ?_, hc⟩
  rw [hcount G fun c hc => Graph.length_le_of_mem_perfectMatchingInstance hdeg hc,
    Graph.partitionFunction_perfectMatchingInstance]

end Cslib.Complexity.ContractionMatching
