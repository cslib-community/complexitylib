/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space.TQBF.Formula
public import Complexity.Computability.Complexity.CookLevin.Correctness
public import Complexity.Computability.Complexity.CookLevin.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Savitch
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run

/-!
# The reduction to `TQBF`

Acceptance of a nondeterministic machine within polynomial space is reachability of the accepting
code from the code of the initial view, along the edges between the codes of its finite views
(`Turing.MultiTapeNTM.savitchDecide_eq_true_iff`). This file writes this reachability as a closed
quantified Boolean formula [Sipser, Theorem 8.9][Sipser2013]
[Arora and Barak, Theorem 4.13][AroraBarak09]: Savitch's formula
(`Cslib.Complexity.TQBF.savitchFormula`) on the codes, of width `w = 2 * W + 2` for the width `W`
of the codes, at depth `w`. Each of its `w` levels has `O(w)` tokens, so it has `O(w ^ 2)` tokens
besides those of its formula of level `0`; it is computed in polynomial time in
`Cslib.Computability.Complexity.Classes.Space.TQBF.PolyTime`.

Its formula of level `0` must express one step or none between the words held by two blocks. The
step test of codes is polynomial-time (`Cslib.Complexity.TQBF.computableInPolyTime_edgeTest`),
so some tidy machine computes, on `encPair enc encBits (a, x ++ y)`, the Boolean
`Cslib.Reachability.reach e w 0 x y` for the edge test `e` of the codes, within a polynomial time
bound `T`. Its Cook–Levin tableau (`Cslib.Complexity.CookLevin.tableau`) on the inputs
`frame (enc a) ++ z` with `|z| = 2 * w`, unrolled for `T` steps, has a satisfying assignment with
certificate bits `z` exactly when the machine accepts `frame (enc a) ++ z`
(`Cslib.Complexity.CookLevin.exists_eval_tableau_iff`). The formula of level `0`
(`Cslib.Complexity.TQBF.baseFormula`) numbers the variables of the tableau by odd numbers, links
its certificate variables to the source and target blocks of level `0`, and quantifies all of them
existentially (`Cslib.Complexity.TQBF.eval_baseFormula`); its free variables are the blocks.

## Main definitions

* `Cslib.Complexity.TQBF.tabVar`: the numbering of the tableau variables by odd numbers.
* `Cslib.Complexity.TQBF.baseFormula`: a tableau as a formula on the blocks of level `0`.
* `Cslib.Complexity.TQBF.edgeTest`: the test of one step or none between codes.
* `Cslib.Complexity.TQBF.reduce`: the reduction.

## Main results

* `Cslib.Complexity.TQBF.eval_baseFormula`, `Cslib.Complexity.TQBF.mem_freeVars_baseFormula`: the
  formula of level `0`.
* `Cslib.Complexity.TQBF.reduce_mem_TQBF_iff`: the reduction is correct.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.9][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.13][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.TQBF

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL Cslib.Reachability

/-! ### A tableau as the formula of level `0` -/

section Base

variable {k : ℕ} {State : Type} [Fintype State]

/-- The tableau variables, numbered by odd numbers. -/
noncomputable def tabVar (v : CookLevin.Var k State) : ℕ := 2 * v.index + 1

theorem tabVar_injective : Function.Injective (tabVar (k := k) (State := State)) := fun _ _ h =>
  CookLevin.Var.index_injective (by simpa [tabVar] using h)

theorem tabVar_mod_two (v : CookLevin.Var k State) : tabVar v % 2 = 1 := by
  simp [tabVar]

/-- The variable of a block of level `0` holding the `j`-th certificate bit: the source block for
the first `w` bits, then the target block. -/
def certVar (w j : ℕ) : ℕ := if j < w then blockVar 0 0 j else blockVar 1 0 (j - w)

/-- The certificate variables read the words held by the source and target blocks of level `0`. -/
private theorem map_certVar (σ : ℕ → Bool) (w : ℕ) :
    (List.range (2 * w)).map (fun j => σ (certVar w j)) = block σ w 0 0 ++ block σ w 1 0 := by
  have hlen : ((List.range (2 * w)).map fun j => σ (certVar w j)).length =
      (block σ w 0 0 ++ block σ w 1 0).length := by
    rw [List.length_map, List.length_range, List.length_append, length_block, length_block, two_mul]
  refine List.ext_getElem hlen fun j h₁ h₂ => ?_
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range, certVar]
  by_cases hj : j < w
  · rw [List.getElem_append_left (by simpa [block, blockVars] using hj)]
    simp [hj, block, blockVars]
  · rw [List.getElem_append_right (by simpa [block, blockVars] using hj)]
    simp [hj, block, blockVars]

/-- The variables quantified in the formula of level `0`: the variables of the tableau and its
first `2 * w` certificate variables. -/
noncomputable def baseVars (tab : CNF (CookLevin.Var k State)) (w : ℕ) : List ℕ :=
  tab.vars.map tabVar ++
    (List.range (2 * w)).map fun j => tabVar (CookLevin.Var.cert (k := k) (State := State) j)

/-- The links of the certificate variables to the blocks of level `0`. -/
noncomputable def certLinks (k : ℕ) (State : Type) [Fintype State] (w : ℕ) : QBF ℕ :=
  QBF.conj ((List.range (2 * w)).map fun j =>
    QBF.iff (.var (tabVar (CookLevin.Var.cert (k := k) (State := State) j))) (.var (certVar w j)))

/-- **A tableau as the formula of level `0`**: its variables numbered by odd numbers, its first
`2 * w` certificate variables linked to the source and target blocks of level `0`, and all of them
quantified existentially. -/
noncomputable def baseFormula (tab : CNF (CookLevin.Var k State)) (w : ℕ) : QBF ℕ :=
  QBF.exs (baseVars tab w) (.and (certLinks k State w) (QBF.ofCNF (tab.relabel tabVar)))

/-- Block variables are not quantified in the formula of level `0`. -/
private theorem certVar_notMem_baseVars (tab : CNF (CookLevin.Var k State)) (w j : ℕ) :
    certVar w j ∉ baseVars tab w := by
  have h : certVar w j % 2 = 0 := by unfold certVar; split_ifs <;> exact blockVar_mod_two ..
  simp only [baseVars, List.mem_append, List.mem_map, not_or, not_exists, not_and]
  exact ⟨fun v _ hv => by have := tabVar_mod_two v; omega,
    fun i _ hv => by have := tabVar_mod_two (CookLevin.Var.cert (k := k) (State := State) i); omega⟩

/-- **The formula of level `0` holds** exactly when the tableau has a satisfying assignment whose
first `2 * w` certificate bits are the words held by the source and target blocks of level `0`. -/
theorem eval_baseFormula (tab : CNF (CookLevin.Var k State)) (w : ℕ) (σ : ℕ → Bool) :
    (baseFormula tab w).eval σ = true ↔ ∃ τ : CookLevin.Var k State → Bool,
      CookLevin.certWord τ (2 * w) = block σ w 0 0 ++ block σ w 1 0 ∧ tab.eval τ = true := by
  classical
  rw [baseFormula, QBF.eval_exs_eq_true_iff]
  constructor
  · rintro ⟨σ', hσ', h⟩
    simp only [QBF.eval_and, Bool.and_eq_true, certLinks, QBF.eval_conj, List.all_map,
      List.all_eq_true, List.mem_range, Function.comp_apply, QBF.eval_iff, QBF.eval_var, beq_iff_eq,
      QBF.eval_ofCNF, CNF.eval_relabel] at h
    obtain ⟨hlink, htab⟩ := h
    refine ⟨σ' ∘ tabVar, ?_, htab⟩
    rw [← map_certVar]
    simp only [CookLevin.certWord, Function.comp_apply]
    exact List.map_inj_left.mpr fun j hj => (hlink j (List.mem_range.mp hj)).trans
      (hσ' _ (certVar_notMem_baseVars tab w j))
  · rintro ⟨τ, hcert, htab⟩
    let σ' : ℕ → Bool := fun x =>
      if h : x ∈ baseVars tab w ∧ ∃ v, tabVar v = x then τ h.2.choose else σ x
    have hσ' (v : CookLevin.Var k State) (hv : tabVar v ∈ baseVars tab w) :
        σ' (tabVar v) = τ v := by
      have h : tabVar v ∈ baseVars tab w ∧ ∃ v', tabVar v' = tabVar v := ⟨hv, v, rfl⟩
      simp only [σ', h]
      exact congrArg τ (tabVar_injective h.2.choose_spec)
    refine ⟨σ', fun x hx => by simp [σ', hx], ?_⟩
    simp only [QBF.eval_and, Bool.and_eq_true, certLinks, QBF.eval_conj, List.all_map,
      List.all_eq_true, List.mem_range, Function.comp_apply, QBF.eval_iff, QBF.eval_var, beq_iff_eq,
      QBF.eval_ofCNF, CNF.eval_relabel]
    refine ⟨fun j hj => ?_, ?_⟩
    · have hmem : tabVar (CookLevin.Var.cert (k := k) (State := State) j) ∈ baseVars tab w :=
        List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      rw [hσ' _ hmem, show σ' (certVar w j) = σ (certVar w j) by
        simp [σ', certVar_notMem_baseVars tab w j]]
      have := congrArg (fun l => l[j]?) (hcert.trans (map_certVar σ w).symm)
      simpa [CookLevin.certWord, List.getElem?_range, hj] using this
    · rw [← htab]
      exact CNF.eval_congr fun v hv => hσ' v (List.mem_append_left _ (List.mem_map_of_mem hv))

/-- The free variables of the formula of level `0` lie in the source and target blocks of
level `0`. -/
theorem mem_freeVars_baseFormula (tab : CNF (CookLevin.Var k State)) (w : ℕ) :
    ∀ x ∈ (baseFormula tab w).freeVars, x ∈ blockVars w 0 0 ∨ x ∈ blockVars w 1 0 := by
  intro x hx
  simp only [baseFormula, QBF.freeVars_exs, QBF.freeVars_and, Finset.mem_sdiff, Finset.mem_union,
    List.mem_toFinset] at hx
  obtain ⟨hx, hbase⟩ := hx
  rcases hx with hx | hx
  · simp only [certLinks, QBF.mem_freeVars_conj, List.mem_map, List.mem_range] at hx
    obtain ⟨_, ⟨j, hj, rfl⟩, hx⟩ := hx
    simp only [QBF.freeVars_iff, QBF.freeVars_var, Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact absurd (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
        hbase
    · unfold certVar
      split_ifs with h
      · exact .inl (List.mem_map.mpr ⟨j, List.mem_range.mpr h, rfl⟩)
      · exact .inr (List.mem_map.mpr ⟨j - w, List.mem_range.mpr (by omega), rfl⟩)
  · rw [QBF.mem_freeVars_ofCNF] at hx
    simp only [CNF.vars, CNF.relabel, Clause.relabel, List.mem_map, List.mem_flatten] at hx
    obtain ⟨⟨y, b⟩, ⟨_, ⟨c, hc, rfl⟩, hl⟩, rfl⟩ := hx
    obtain ⟨⟨v, b'⟩, hv, hl⟩ := List.mem_map.mp hl
    simp only [Prod.map, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    refine absurd (List.mem_append_left _ (List.mem_map_of_mem ?_)) hbase
    simp only [CNF.vars, List.mem_map, List.mem_flatten]
    exact ⟨(v, b'), ⟨c, hc, hv⟩, rfl⟩

end Base

/-! ### The reduction -/

section Reduction

variable {α : Type} (enc : α ↪ List Bool) {k : ℕ} {State : Type} [Finite State]
  (ntm : MultiTapeNTM k Bool State) (c d : ℕ)

/-- The width of the words of the reduction on `a`: the codes of the views of `ntm` on `enc a`,
of `2 * W + 2` bits for the width `W` of `Turing.MultiTapeNTM.codeWidth`. -/
noncomputable def width (a : α) : ℕ := 2 * ntm.codeWidth c d (enc a) + 2

/-- **The test of one step or none between codes**, on the instance `a` and the concatenation of
the two codes. -/
noncomputable def edgeTest (p : α × List Bool) : Bool :=
  reach ntm.codeEdge (width enc ntm c d p.1) 0 (p.2.take (width enc ntm c d p.1))
    (p.2.drop (width enc ntm c d p.1))

/-- The time allowed to a machine computing the test on `encPair enc encBits (a, z)` with
`|z| = 2 * width enc ntm c d a`, for the time bound `cV * (n + 1) ^ dV`. -/
noncomputable def edgeTime (cV dV : ℕ) (a : α) : ℕ :=
  cV * (2 * (enc a).length + 2 * width enc ntm c d a + 2) ^ dV

/-- **The reduction to `TQBF`**: Savitch's formula on the codes of the views of `ntm` on `enc a`,
from the code of the initial view to the accepting code, with the Cook–Levin tableau of the
machine `tmV` computing the test of one step or none as its formula of level `0`. -/
noncomputable def reduce {kV : ℕ} {StateV : Type} [Fintype StateV] [DecidableEq StateV]
    (tmV : MultiTapeTM kV Bool StateV) (cV dV : ℕ) (a : α) : QBF ℕ :=
  savitchFormula (width enc ntm c d a) (width enc ntm c d a)
    (baseFormula (CookLevin.tableau tmV (frame (enc a)) (2 * width enc ntm c d a)
      (edgeTime enc ntm c d cV dV a)) (width enc ntm c d a))
    (MultiTapeNTM.viewCode (ntm.codeWidth c d (enc a)) (ntm.initView (enc a)))
    (MultiTapeNTM.acceptCode (ntm.codeWidth c d (enc a)))

variable {enc ntm c d}

/-- **The reduction is correct.** If `tmV` computes the test of one step or none tidily within time
`cV * (n + 1) ^ dV`, and every computation path of `ntm` on `enc a` visits at most
`c * ((enc a).length + 1) ^ d` work cells, then the formula of `a` is a true closed formula
exactly when `ntm` accepts `enc a`. -/
theorem reduce_mem_TQBF_iff {kV : ℕ} {StateV : Type} [Fintype StateV] [DecidableEq StateV]
    {tmV : MultiTapeTM kV Bool StateV} {cV dV : ℕ} {sV : α × List Bool → ℕ}
    (htm : tmV.ComputesFunTidilyInTimeAndSpace (encPair enc encBits) encBool (edgeTest enc ntm c d)
      (fun x => cV * ((encPair enc encBits x).length + 1) ^ dV) sV)
    {a : α} {s : ℕ} (hs : ntm.RunsInSpace (enc a) s) (hsc : s ≤ c * ((enc a).length + 1) ^ d) :
    reduce enc ntm c d tmV cV dV a ∈ TQBF ↔ ntm.Accepts (enc a) := by
  set W := ntm.codeWidth c d (enc a)
  set w := width enc ntm c d a with hw_def
  -- the formula of level `0` is the test of one step or none
  have hbase (σ : ℕ → Bool) : (baseFormula (CookLevin.tableau tmV (frame (enc a)) (2 * w)
      (edgeTime enc ntm c d cV dV a)) w).eval σ =
        reach ntm.codeEdge w 0 (block σ w 0 0) (block σ w 1 0) := by
    set z := block σ w 0 0 ++ block σ w 1 0
    have hz : z.length = 2 * w := by simp only [z, List.length_append, length_block]; omega
    have hrun := (htm (a, z)).runFrom_initCfg
    have hlen : (encPair enc encBits (a, z)).length = 2 * (enc a).length + 2 * w + 1 := by
      rw [length_encPair, encBits_apply, hz]
      dsimp only
      omega
    dsimp only at hrun
    rw [hlen, encPair_apply, encBits_apply] at hrun
    rw [Bool.eq_iff_iff, eval_baseFormula, ← hz, CookLevin.exists_eval_tableau_iff,
      show edgeTime enc ntm c d cV dV a = cV * (2 * (enc a).length + 2 * w + 1 + 1) ^ dV by
        rw [edgeTime, ← hw_def]]
    rw [hrun.2]
    simp only [encBool_apply, List.cons.injEq, and_true, edgeTest]
    have htake : z.take w = block σ w 0 0 := List.take_left' (length_block ..)
    have hdrop : z.drop w = block σ w 1 0 := List.drop_left' (length_block ..)
    rw [htake, hdrop]
    exact ⟨fun h => h.2, fun h => ⟨hrun.1, h⟩⟩
  have hsrc : (MultiTapeNTM.viewCode W (ntm.initView (enc a))).length = w :=
    MultiTapeNTM.length_viewCode (Nat.le_add_right _ _)
  have hdst : (MultiTapeNTM.acceptCode W).length = w := List.length_replicate ..
  rw [reduce, ← hw_def, mem_TQBF_iff_of_closed (closed_savitchFormula
    (mem_freeVars_baseFormula _ _) _ _ _) (fun _ => false), eval_savitchFormula hbase _ hsrc hdst,
    ← savitch_eq, ← MultiTapeNTM.savitchDecide_eq_true_iff hs hsc]
  rfl

end Reduction

end Cslib.Complexity.TQBF
