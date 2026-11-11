/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Tseitin
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import Mathlib.Data.List.GetD

/-!
# Sequential exact-one De Morgan circuits and width-3 Tseitin compilation

For a list of input wires `ws`, `seqExactlyOneClause n base ws` builds a De Morgan gate list of
only `3 * ws.length + 3` gates (`O(ws.length)` gates rather than quadratic pairwise clauses) whose
output wire evaluates to `true` exactly when precisely one wire in `ws` is `true`. Repeating across
a family `wss` of wire lists (`seqExactlyOneAll n wss`) yields a gate list of
`1 + 4 * wss.length + 3 * (wss.map List.length).sum` gates, and `tseitinSatCNF [] n gates out`
compiles it to a width-`3` CNF formula preserving the exact number of satisfying input bitstrings
in `O(n + ∑ |ws|)` variables.

## Main definitions

* `Cslib.Circuits.Boolean.tseitinSatAssignmentEquiv`: explicit bijection between satisfying input
  bitstrings and `tseitinSatCNF` models on `Finset.range (n + gates.length)`.
* `Cslib.Circuits.Boolean.seqExactlyOneClause`: `O(d)`-gate sequential exact-one De Morgan gadget.
* `Cslib.Circuits.Boolean.seqExactlyOneAll`: `O(|wss| + ∑ |ws|)`-gate conjunction of exact-one
  constraints.

## Main results

* `Cslib.Circuits.Boolean.vars_tseitinSatCNF_subset`: occurring-variable bound for `tseitinSatCNF`.
* `Cslib.Circuits.Boolean.isCodeFrom_seqExactlyOneClause`,
  `Cslib.Circuits.Boolean.isCodeFrom_seqExactlyOneAll`: well-formedness (`IsCodeFrom`).
* `Cslib.Circuits.Boolean.evalOutput_seqExactlyOneAll`: exact evaluation correctness.
* `Cslib.Circuits.Boolean.card_evalOutput_eq_modelCountOn_tseitinSatCNF`: exact model-count
  preservation of any well-formed De Morgan gate list compiled via `tseitinSatCNF [] n gates o`.
-/

public section

namespace Cslib.Circuits.Boolean

open Cslib.Logic.PL

/-! ### Prefix model-count preservation for `tseitinSatCNF` -/

private theorem eq_evalCode_of_eval_tseitinSatCNF {n : ℕ} {gates : List (Op × List ℕ)} {o : ℕ}
    (hcode : Program.IsCodeFrom signature n 0 gates) {σ : ℕ → Bool}
    (hσ : (tseitinSatCNF [] n gates o).eval σ = true) :
    ∀ w < n + gates.length, σ w =
      (evalCode interpretation false (List.ofFn fun i : Fin n => σ i) gates).getD w false := by
  have h := (eval_tseitinSatCNF_eq_true_iff [] n gates o σ).mp hσ
  exact (eval_tseitinCNF_eq_true_iff_evalCode hcode σ).mp h.2.2

/-- Explicit assignment bijection between bit strings accepted by a single-output well-formed
gate list and satisfying assignments of `tseitinSatCNF [] n gates o` on
`Finset.range (n + gates.length)`. -/
def tseitinSatAssignmentEquiv {n : ℕ} {gates : List (Op × List ℕ)} {o : ℕ}
    (hcode : Program.IsCodeFrom signature n 0 gates) (ho : o < n + gates.length) :
    {x : Fin n → Bool // evalOutput (List.ofFn x) gates o = true} ≃
      {σ : Finset.range (n + gates.length) → Bool //
        (tseitinSatCNF [] n gates o).eval
          (fun w => if hw : w ∈ Finset.range (n + gates.length) then σ ⟨w, hw⟩ else false) =
            true} where
  toFun x :=
    ⟨fun w => (evalCode interpretation false (List.ofFn x.1) gates).getD w.1 false, by
      let vals := evalCode interpretation false (List.ofFn x.1) gates
      let ext : ℕ → Bool := fun w =>
        if hw : w ∈ Finset.range (n + gates.length) then vals.getD w false else false
      have hin (i : ℕ) (hi : i < n) : vals.getD i false = x.1 ⟨i, hi⟩ := by
        obtain ⟨r, hr⟩ := prefix_evalCode interpretation false (List.ofFn x.1) gates
        dsimp [vals]
        rw [← hr, List.getD_append _ _ _ _ (by simp [hi]),
          List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      have hext (w : ℕ) (hw : w < n + gates.length) : ext w = vals.getD w false := by
        dsimp only [ext]
        simp only [Finset.mem_range.mpr hw, ↓reduceDIte]
      have heqFn : (List.ofFn fun i : Fin n => ext i) = List.ofFn x.1 := by
        refine List.ext_getElem (by simp) fun i h₁ _ => ?_
        have hi : i < n := by simpa using h₁
        rw [List.getElem_ofFn, List.getElem_ofFn,
          hext i (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)), hin i hi]
      have hcnf : (tseitinCNF n gates).eval ext = true := by
        rw [eval_tseitinCNF_eq_true_iff_evalCode hcode ext, heqFn]
        exact hext
      rw [eval_tseitinSatCNF_eq_true_iff]
      refine ⟨?_, fun i hi => by simp at hi, hcnf⟩
      change ext o = true
      rw [hext o ho]
      exact x.2⟩
  invFun σ :=
    ⟨fun i => σ.1 ⟨i.1, Finset.mem_range.mpr (Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _))⟩, by
      let ext : ℕ → Bool := fun w =>
        if hw : w ∈ Finset.range (n + gates.length) then σ.1 ⟨w, hw⟩ else false
      have hval := eq_evalCode_of_eval_tseitinSatCNF hcode σ.2 o ho
      have ho' := ((eval_tseitinSatCNF_eq_true_iff [] n gates o ext).mp σ.2).1
      have hof : (List.ofFn fun i : Fin n =>
          σ.1 ⟨i.1, Finset.mem_range.mpr (Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _))⟩) =
          List.ofFn fun i : Fin n => ext i := by
        refine List.ext_getElem (by simp) fun i h₁ _ => ?_
        have hi : i < n := by simpa using h₁
        have hmi : i ∈ Finset.range (n + gates.length) :=
          Finset.mem_range.mpr (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _))
        dsimp only [ext]
        simp only [List.getElem_ofFn, hmi, ↓reduceDIte]
      rw [hof, evalOutput, ← hval]
      change ext o = true
      exact ho'⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    ext i
    obtain ⟨r, hr⟩ := prefix_evalCode interpretation false (List.ofFn x) gates
    change (evalCode interpretation false (List.ofFn x) gates).getD i.1 false = x i
    rw [← hr, List.getD_append _ _ _ _ (by simp [i.2]),
      List.getD_eq_getElem _ _ (by simp [i.2])]
    simp
  right_inv σ := by
    obtain ⟨σ, hσ⟩ := σ
    ext w
    change (evalCode interpretation false (List.ofFn fun i : Fin n =>
      σ ⟨i.1, Finset.mem_range.mpr (Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _))⟩)
      gates).getD w.1 false = σ w
    let ext : ℕ → Bool := fun u =>
      if hu : u ∈ Finset.range (n + gates.length) then σ ⟨u, hu⟩ else false
    have hval := eq_evalCode_of_eval_tseitinSatCNF hcode hσ w.1 (Finset.mem_range.mp w.2)
    have hof : (List.ofFn fun i : Fin n =>
        σ ⟨i.1, Finset.mem_range.mpr (Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _))⟩) =
        List.ofFn fun i : Fin n => ext i := by
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      have hi : i < n := by simpa using h₁
      have hmi : i ∈ Finset.range (n + gates.length) :=
        Finset.mem_range.mpr (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _))
      dsimp only [ext]
      simp only [List.getElem_ofFn, hmi, ↓reduceDIte]
    rw [hof, ← hval]
    simp only [w.2, ↓reduceDIte]

/-- **`tseitinSatCNF` preserves the exact number of accepting input bitstrings.** -/
theorem card_evalOutput_eq_modelCountOn_tseitinSatCNF {n : ℕ} {gates : List (Op × List ℕ)} {o : ℕ}
    (hcode : Program.IsCodeFrom signature n 0 gates) (ho : o < n + gates.length) :
    (Finset.univ.filter fun x : Fin n → Bool => evalOutput (List.ofFn x) gates o = true).card =
      (tseitinSatCNF [] n gates o).modelCountOn (Finset.range (n + gates.length)) := by
  classical
  rw [CNF.modelCountOn, ← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr ((Equiv.subtypeEquivRight (by simp)).trans
    ((tseitinSatAssignmentEquiv hcode ho).trans (Equiv.subtypeEquivRight (by simp))))

/-- Every occurring variable of `tseitinSatCNF [] n gates o` is strictly below `n + gates.length`
when `gates` is well-formed (`IsCodeFrom signature n 0 gates`) and `o < n + gates.length`. -/
theorem vars_tseitinSatCNF_subset {n : ℕ} {gates : List (Op × List ℕ)} {o : ℕ}
    (hcode : Program.IsCodeFrom signature n 0 gates) (ho : o < n + gates.length)
    (hpos : 0 < n + gates.length) :
    (tseitinSatCNF [] n gates o).vars.toFinset ⊆ Finset.range (n + gates.length) := by
  intro v hv
  rw [List.mem_toFinset, CNF.vars, List.mem_map] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  rw [List.mem_flatten] at hl
  obtain ⟨c, hc, hl⟩ := hl
  rw [tseitinSatCNF, List.mapIdx_nil, List.mem_append, List.mem_singleton] at hc
  rcases hc with rfl | hc
  · simp only [unitClause, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> exact Finset.mem_range.mpr ho
  · simp only [tseitinCNF, List.mem_flatMap, List.mem_finRange, true_and, gateClauses,
      List.mem_ofFn] at hc
    obtain ⟨g, j, rfl⟩ := hc
    have hlt := hcode.getElem g g.isLt
    have harg (idx : ℕ) : gates[g].2.getD idx 0 ∈ Finset.range (n + gates.length) := by
      by_cases hidx : idx < gates[g].2.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
        exact Finset.mem_range.mpr ((hlt.2 _ (List.getElem_mem hidx)).trans (by omega))
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
        exact Finset.mem_range.mpr hpos
    rcases mem_tseitinClause hl with h1 | h1 | h1
    · rw [h1]
      exact Finset.mem_range.mpr (by omega)
    · rw [h1]
      exact harg 0
    · rw [h1]
      exact harg 1

/-! ### `IsCodeFrom` and single-gate `evalCode` helpers -/

private theorem isCodeFrom_const (n k : ℕ) (v : Bool) (rest : List (Op × List ℕ))
    (hrest : Program.IsCodeFrom signature n (k + 1) rest) :
    Program.IsCodeFrom signature n k ((Op.const v, []) :: rest) :=
  ⟨⟨rfl, fun _ h => by simp at h⟩, hrest⟩

private theorem isCodeFrom_not (n k a : ℕ) (rest : List (Op × List ℕ))
    (ha : a < n + k) (hrest : Program.IsCodeFrom signature n (k + 1) rest) :
    Program.IsCodeFrom signature n k ((Op.not, [a]) :: rest) :=
  ⟨⟨rfl, fun i hi => by simp only [List.mem_singleton] at hi; exact hi ▸ ha⟩, hrest⟩

private theorem isCodeFrom_bin (n k : ℕ) (op : Op) (har : signature.Arity op = 2)
    (a b : ℕ) (rest : List (Op × List ℕ)) (ha : a < n + k) (hb : b < n + k)
    (hrest : Program.IsCodeFrom signature n (k + 1) rest) :
    Program.IsCodeFrom signature n k ((op, [a, b]) :: rest) := by
  refine ⟨⟨har.symm, fun i hi => ?_⟩, hrest⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> assumption

private theorem getD_evalCode_prefix {x : List Bool} {gates rest : List (Op × List ℕ)}
    {u : ℕ} (hu : u < x.length + gates.length) :
    (evalCode interpretation false x (gates ++ rest)).getD u false =
      (evalCode interpretation false x gates).getD u false := by
  rw [evalCode_append]
  obtain ⟨r, hr⟩ := prefix_evalCode interpretation false (evalCode interpretation false x gates)
    rest
  have hlen : (evalCode interpretation false x gates).length = x.length + gates.length :=
    length_evalCode ..
  rw [← hr, List.getD_append _ _ _ _ (hlen ▸ hu)]

private theorem getD_evalCode_append_const {x : List Bool} {gates : List (Op × List ℕ)}
    (v : Bool) :
    (evalCode interpretation false x (gates ++ [(.const v, [])])).getD
        (x.length + gates.length) false = v := by
  rw [evalCode_append_singleton]
  have hlen : (evalCode interpretation false x gates).length = x.length + gates.length :=
    length_evalCode ..
  rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
  rfl

private theorem getD_evalCode_append_not {x : List Bool} {gates : List (Op × List ℕ)} (a : ℕ) :
    (evalCode interpretation false x (gates ++ [(.not, [a])])).getD
        (x.length + gates.length) false =
      !((evalCode interpretation false x gates).getD a false) := by
  rw [evalCode_append_singleton]
  have hlen : (evalCode interpretation false x gates).length = x.length + gates.length :=
    length_evalCode ..
  rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
  rfl

private theorem getD_evalCode_append_bin {x : List Bool} {gates : List (Op × List ℕ)}
    (op : Op) (a b : ℕ) :
    (evalCode interpretation false x (gates ++ [(op, [a, b])])).getD
        (x.length + gates.length) false =
      op.value ((evalCode interpretation false x gates).getD a false)
        ((evalCode interpretation false x gates).getD b false) := by
  rw [evalCode_append_singleton]
  have hlen : (evalCode interpretation false x gates).length = x.length + gates.length :=
    length_evalCode ..
  rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
  cases op <;> rfl

/-! ### Sequential exact-one De Morgan gate list -/

structure SeqExactlyOneStepResult where
  gates : List (Op × List ℕ)
  seen1Wire : ℕ
  seen2Wire : ℕ
  deriving Inhabited

/-- Recursive linear-size state transition tracking `(seen1, seen2)` across wire list `ws`.
Returns `(gates, seen1Wire, seen2Wire)`. -/
@[expose] def seqExactlyOneStep (nextWire seen1 seen2 : ℕ) : List ℕ → SeqExactlyOneStepResult
  | [] => ⟨[], seen1, seen2⟩
  | w :: ws =>
    let both := nextWire
    let nextSeen2 := nextWire + 1
    let nextSeen1 := nextWire + 2
    let rest := seqExactlyOneStep (nextWire + 3) nextSeen1 nextSeen2 ws
    ⟨[(.and, [seen1, w]), (.or, [seen2, both]), (.or, [seen1, w])] ++ rest.gates,
      rest.seen1Wire, rest.seen2Wire⟩

/-- Sequential exact-one circuit on input wires `ws`, starting at gate offset `base` on `n` total
input wires. Returns `(gates, outputWire)`. Uses `3 * ws.length + 3` gates. -/
@[expose] def seqExactlyOneClause (n base : ℕ) (ws : List ℕ) : ExactOneCircuitResult :=
  let zeroWire := n + base
  let step := seqExactlyOneStep (n + base + 1) zeroWire zeroWire ws
  let seenPair := (step.seen1Wire, step.seen2Wire)
  let notWire := n + base + 1 + step.gates.length
  let outWire := notWire + 1
  { gates := [(.const false, [])] ++ step.gates ++ [(.not, [seenPair.2]), (.and, [seenPair.1, notWire])],
    outWire := outWire }

@[simp]
theorem length_seqExactlyOneStep (nextWire seen1 seen2 : ℕ) (ws : List ℕ) :
    (seqExactlyOneStep nextWire seen1 seen2 ws).gates.length = 3 * ws.length := by
  induction ws generalizing nextWire seen1 seen2 with
  | nil => rfl
  | cons w ws ih =>
    simp only [seqExactlyOneStep, List.length_append, List.length_cons, List.length_nil, ih]
    omega

@[simp]
theorem length_seqExactlyOneClause (n base : ℕ) (ws : List ℕ) :
    (seqExactlyOneClause n base ws).gates.length = 3 * ws.length + 3 := by
  simp only [seqExactlyOneClause, List.length_append, List.length_cons, List.length_nil,
    length_seqExactlyOneStep]
  omega

theorem snd_seqExactlyOneClause (n base : ℕ) (ws : List ℕ) :
    (seqExactlyOneClause n base ws).outWire = n + base + 3 * ws.length + 2 := by
  simp only [seqExactlyOneClause, length_seqExactlyOneStep]
  omega

private theorem isCodeFrom_seqExactlyOneStep (n : ℕ) :
    ∀ (ws : List ℕ) (k seen1 seen2 : ℕ),
      (∀ w ∈ ws, w < n + k) → seen1 < n + k → seen2 < n + k →
        Program.IsCodeFrom signature n k (seqExactlyOneStep (n + k) seen1 seen2 ws).gates ∧
        (seqExactlyOneStep (n + k) seen1 seen2 ws).seen1Wire <
          n + (k + (seqExactlyOneStep (n + k) seen1 seen2 ws).gates.length) ∧
        (seqExactlyOneStep (n + k) seen1 seen2 ws).seen2Wire <
          n + (k + (seqExactlyOneStep (n + k) seen1 seen2 ws).gates.length)
  | [], k, seen1, seen2, _, hs1, hs2 => by
    simp only [seqExactlyOneStep, List.length_nil, Nat.add_zero]
    exact ⟨trivial, hs1, hs2⟩
  | w :: ws, k, seen1, seen2, hws, hs1, hs2 => by
    have hw : w < n + k := hws w (List.mem_cons_self ..)
    have hrest := isCodeFrom_seqExactlyOneStep n ws (k + 3) (n + k + 2) (n + k + 1)
      (fun u hu => by have := hws u (List.mem_cons_of_mem _ hu); omega) (by omega) (by omega)
    dsimp only [seqExactlyOneStep]
    rw [show n + k + 3 = n + (k + 3) from by omega]
    refine ⟨?_, ?_, ?_⟩
    · refine isCodeFrom_bin n k .and rfl seen1 w _ hs1 hw ?_
      refine isCodeFrom_bin n (k + 1) .or rfl seen2 (n + k) _ (by omega) (by omega) ?_
      refine isCodeFrom_bin n (k + 2) .or rfl seen1 w _ (by omega) (by omega) ?_
      change Program.IsCodeFrom signature n (k + 3)
        (seqExactlyOneStep (n + (k + 3)) (n + (k + 2)) (n + (k + 1)) ws).gates
      exact hrest.gates
    · simp only [List.length_cons, List.length_nil, List.length_append]
      omega
    · simp only [List.length_cons, List.length_nil, List.length_append]
      omega

/-- `seqExactlyOneClause n base ws` is well-formed starting at gate `base` whenever all wires in
`ws` are `< n + base`. -/
theorem isCodeFrom_seqExactlyOneClause (n base : ℕ) {ws : List ℕ} (hws : ∀ w ∈ ws, w < n + base) :
    Program.IsCodeFrom signature n base (seqExactlyOneClause n base ws).gates := by
  have hstep := isCodeFrom_seqExactlyOneStep n ws (base + 1) (n + base) (n + base)
    (fun u hu => (hws u hu).trans (by omega)) (by omega) (by omega)
  have hbase : n + base + 1 = n + (base + 1) := by omega
  rw [seqExactlyOneClause, List.append_assoc, List.singleton_append]
  refine isCodeFrom_const n base false _ ?_
  rw [hbase, Program.isCodeFrom_append]
  refine ⟨hstep.1, ?_⟩
  refine isCodeFrom_not n (base + 1 + _) _ _ (by have := hstep.2.2; omega) ?_
  exact isCodeFrom_bin n (base + 1 + _ + 1) .and rfl _ _ []
    (by have := hstep.2.1; omega) (by omega) trivial

private theorem evalCode_seqExactlyOneStep (x : List Bool) (prefixGates : List (Op × List ℕ))
    (ws : List ℕ) (seen1 seen2 : ℕ) (count : ℕ)
    (hws : ∀ w ∈ ws, w < x.length + prefixGates.length)
    (hs1_lt : seen1 < x.length + prefixGates.length)
    (hs2_lt : seen2 < x.length + prefixGates.length)
    (hs1 : (evalCode interpretation false x prefixGates).getD seen1 false = decide (0 < count))
    (hs2 : (evalCode interpretation false x prefixGates).getD seen2 false = decide (1 < count)) :
    let res := seqExactlyOneStep (x.length + prefixGates.length) seen1 seen2 ws
    let full := evalCode interpretation false x (prefixGates ++ res.gates)
    full.getD res.seen1Wire false = decide (0 < count + ws.countP fun w => full.getD w false) ∧
      full.getD res.seen2Wire false = decide (1 < count + ws.countP fun w => full.getD w false) := by
  induction ws generalizing prefixGates seen1 seen2 count with
  | nil =>
    dsimp only [seqExactlyOneStep]
    simpa using And.intro hs1 hs2
  | cons w ws ih =>
    let k := prefixGates.length
    have hw : w < x.length + k := hws w (List.mem_cons_self ..)
    let p1 := prefixGates ++ [(.and, [seen1, w])]
    let p2 := p1 ++ [(.or, [seen2, x.length + k])]
    let p3 := p2 ++ [(.or, [seen1, w])]
    have hp1_len : p1.length = k + 1 := by simp [p1, k]
    have hp2_len : p2.length = k + 2 := by simp [p2, hp1_len]
    have hp3_len : p3.length = k + 3 := by simp [p3, hp2_len]
    have hboth : (evalCode interpretation false x p1).getD (x.length + k) false =
        (decide (0 < count) && (evalCode interpretation false x prefixGates).getD w false) := by
      rw [getD_evalCode_append_bin, Op.value, hs1]
    have hns2 : (evalCode interpretation false x p2).getD (x.length + k + 1) false =
        decide (1 < count +
          if (evalCode interpretation false x prefixGates).getD w false then 1 else 0) := by
      dsimp only [p2]
      rw [show x.length + k + 1 = x.length + p1.length from by omega,
        getD_evalCode_append_bin, Op.value, getD_evalCode_prefix hs2_lt, hs2, hboth]
      cases (evalCode interpretation false x prefixGates).getD w false <;>
        rcases count with _ | _ | c <;> simp [Nat.add_assoc]
    have hns1 : (evalCode interpretation false x p3).getD (x.length + k + 2) false =
        decide (0 < count +
          if (evalCode interpretation false x prefixGates).getD w false then 1 else 0) := by
      dsimp only [p3]
      rw [show x.length + k + 2 = x.length + p2.length from by omega,
        getD_evalCode_append_bin, Op.value]
      have hread_s1 : (evalCode interpretation false x p2).getD seen1 false =
          (evalCode interpretation false x prefixGates).getD seen1 false := by
        dsimp only [p2, p1]
        rw [List.append_assoc, getD_evalCode_prefix hs1_lt]
      have hread_w : (evalCode interpretation false x p2).getD w false =
          (evalCode interpretation false x prefixGates).getD w false := by
        dsimp only [p2, p1]
        rw [List.append_assoc, getD_evalCode_prefix hw]
      rw [hread_s1, hread_w, hs1]
      cases (evalCode interpretation false x prefixGates).getD w false <;>
        rcases count with _ | _ | c <;> simp [Nat.add_assoc]
    have hns2' : (evalCode interpretation false x p3).getD (x.length + k + 1) false =
        decide (1 < count +
          if (evalCode interpretation false x prefixGates).getD w false then 1 else 0) := by
      dsimp only [p3]
      rw [getD_evalCode_prefix (by rw [hp2_len]; omega), hns2]
    have hih := ih p3 (x.length + k + 2) (x.length + k + 1)
      (count + if (evalCode interpretation false x prefixGates).getD w false then 1 else 0)
      (fun u hu => by have := hws u (List.mem_cons_of_mem _ hu); omega)
      (by omega) (by omega) hns1 hns2'
    rw [hp3_len, show x.length + (k + 3) = x.length + k + 3 from by omega] at hih
    let rest := seqExactlyOneStep (x.length + k + 3) (x.length + k + 2) (x.length + k + 1) ws
    have hassoc : p3 ++ rest.gates =
        prefixGates ++ (seqExactlyOneStep (x.length + k) seen1 seen2 (w :: ws)).gates := by
      simp [p3, p2, p1, seqExactlyOneStep, rest, List.append_assoc, Nat.add_assoc]
    have hrestEq1 : (seqExactlyOneStep (x.length + (k + 3)) (x.length + (k + 2))
        (x.length + (k + 1)) ws).seen1Wire =
        (seqExactlyOneStep (x.length + k) seen1 seen2 (w :: ws)).seen1Wire := by
      dsimp only [seqExactlyOneStep]
      rw [show x.length + k + 3 = x.length + (k + 3) from by omega,
        show x.length + k + 2 = x.length + (k + 2) from by omega,
        show x.length + k + 1 = x.length + (k + 1) from by omega]
    have hrestEq2 : (seqExactlyOneStep (x.length + (k + 3)) (x.length + (k + 2))
        (x.length + (k + 1)) ws).seen2Wire =
        (seqExactlyOneStep (x.length + k) seen1 seen2 (w :: ws)).seen2Wire := by
      dsimp only [seqExactlyOneStep]
      rw [show x.length + k + 3 = x.length + (k + 3) from by omega,
        show x.length + k + 2 = x.length + (k + 2) from by omega,
        show x.length + k + 1 = x.length + (k + 1) from by omega]
    change _ ∧ _ at hih
    rw [hassoc] at hih
    have hreadFull (u : ℕ) (hu : u < x.length + k) :
        (evalCode interpretation false x
          (prefixGates ++ (seqExactlyOneStep (x.length + k) seen1 seen2 (w :: ws)).gates)).getD
          u false =
          (evalCode interpretation false x prefixGates).getD u false :=
      getD_evalCode_prefix hu
    have heq0 :
        List.countP (fun u =>
          (evalCode interpretation false x
            (prefixGates ++ (seqExactlyOneStep (x.length + k) seen1 seen2 (w :: ws)).gates)).getD u
            false) (w :: ws) =
        (if (evalCode interpretation false x prefixGates).getD w false then 1 else 0) +
          List.countP (fun u =>
            (evalCode interpretation false x
              (prefixGates ++ (seqExactlyOneStep (x.length + k) seen1 seen2 (w :: ws)).gates)).getD u
              false) ws := by
      rw [List.countP_cons, hreadFull w hw]
      split_ifs <;> omega
    have hres1 : (seqExactlyOneStep (x.length + k) seen1 seen2 (w :: ws)).seen1Wire =
        (seqExactlyOneStep (x.length + (k + 3)) (x.length + (k + 2))
          (x.length + (k + 1)) ws).seen1Wire :=
      hrestEq1.symm
    have hres2 : (seqExactlyOneStep (x.length + k) seen1 seen2 (w :: ws)).seen2Wire =
        (seqExactlyOneStep (x.length + (k + 3)) (x.length + (k + 2))
          (x.length + (k + 1)) ws).seen2Wire :=
      hrestEq2.symm
    change _ ∧ _
    rw [hres1, hres2, heq0]
    simpa only [Nat.add_assoc] using hih

/-- **Evaluation correctness of `seqExactlyOneClause`**: after appending `seqExactlyOneClause`, its
output wire holds `true` iff precisely one wire in `ws` holds `true`. -/
theorem evalCode_seqExactlyOneClause (x : List Bool) (prefixGates : List (Op × List ℕ))
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < x.length + prefixGates.length) :
    let clause := seqExactlyOneClause x.length prefixGates.length ws
    let vals := evalCode interpretation false x (prefixGates ++ clause.1)
    vals.getD clause.2 false =
      decide (ws.countP (fun w => (evalCode interpretation false x prefixGates).getD w false) =
        1) := by
  let k := prefixGates.length
  let clause := seqExactlyOneClause x.length k ws
  let prefix1 := prefixGates ++ [(.const false, [])]
  have hz : (evalCode interpretation false x prefix1).getD (x.length + k) false =
      decide (0 < 0) :=
    getD_evalCode_append_const false
  have hstep := evalCode_seqExactlyOneStep x prefix1 ws (x.length + k) (x.length + k) 0
    (fun w hw => (hws w hw).trans (by simp [prefix1]))
    (by simp [prefix1, k]) (by simp [prefix1, k]) hz hz
  have hlen1 : prefix1.length = k + 1 := by simp [prefix1, k]
  rw [hlen1, show x.length + (k + 1) = x.length + k + 1 from by omega] at hstep
  let stepRes := seqExactlyOneStep (x.length + k + 1) (x.length + k) (x.length + k) ws
  let prefix2 := prefix1 ++ stepRes.gates
  let notWire := x.length + k + 1 + stepRes.gates.length
  let prefix3 := prefix2 ++ [(.not, [stepRes.seen2Wire])]
  have hlen2 : prefix2.length = k + 1 + stepRes.gates.length := by
    dsimp only [prefix2, prefix1]
    rw [List.length_append, List.length_append, List.length_singleton]
  have hlen3 : prefix3.length = k + 1 + stepRes.gates.length + 1 := by
    simp [prefix3, hlen2]
  have hstepCode := isCodeFrom_seqExactlyOneStep x.length ws (k + 1) (x.length + k) (x.length + k)
    (fun u hu => (hws u hu).trans (by omega)) (by omega) (by omega)
  rw [show x.length + (k + 1) = x.length + k + 1 from by omega] at hstepCode
  have hs1lt : stepRes.seen1Wire < x.length + prefix2.length := by
    rw [hlen2]; have := hstepCode.2.1; omega
  have hnot : (evalCode interpretation false x prefix3).getD notWire false =
      !((evalCode interpretation false x prefix2).getD stepRes.seen2Wire false) := by
    dsimp only [prefix3, notWire]
    rw [show x.length + k + 1 + stepRes.gates.length = x.length + prefix2.length by rw [hlen2]; omega]
    exact getD_evalCode_append_not stepRes.seen2Wire
  have hfullEq : prefix3 ++ [(.and, [stepRes.seen1Wire, notWire])] = prefixGates ++ clause.1 := by
    simp [prefix3, prefix2, prefix1, clause, seqExactlyOneClause, stepRes, notWire, k,
      List.append_assoc]
  have hc2 : clause.2 = x.length + prefix3.length := by
    simp [clause, seqExactlyOneClause, hlen3, stepRes, k]; omega
  have hout : (evalCode interpretation false x (prefixGates ++ clause.1)).getD clause.2 false =
      (((evalCode interpretation false x prefix2).getD stepRes.seen1Wire false) &&
        !((evalCode interpretation false x prefix2).getD stepRes.seen2Wire false)) := by
    rw [← hfullEq, hc2, getD_evalCode_append_bin, Op.value, ← hnot]
    have hpre : prefix3 = prefix2 ++ [(.not, [stepRes.seen2Wire])] := rfl
    rw [hpre, getD_evalCode_prefix hs1lt]
  have hcnt : List.countP (fun w => (evalCode interpretation false x prefix2).getD w false) ws =
      List.countP (fun w => (evalCode interpretation false x prefixGates).getD w false) ws := by
    refine List.countP_congr fun w hw => ?_
    have hw' : w < x.length + k := hws w hw
    have hpre : prefix2 = prefixGates ++ ([(.const false, [])] ++ stepRes.gates) := by
      simp [prefix2, prefix1, List.append_assoc]
    rw [hpre, getD_evalCode_prefix hw']
  change (evalCode interpretation false x (prefixGates ++ clause.1)).getD clause.2 false = _
  rw [hout, hstep.1, hstep.2, hcnt]
  simp only [Nat.zero_add]
  rcases List.countP (fun w => (evalCode interpretation false x prefixGates).getD w false) ws with
    _ | _ | _ <;> rfl

/-- Fold a list of wire lists into a conjunction of sequential exact-one De Morgan gadgets.
Returns `(gates, accWire)`. Uses `4 * wss.length + 3 * (wss.map List.length).sum` extra gates. -/
@[expose] def seqExactlyOneFold (n base acc : ℕ) : List (List ℕ) → ExactOneCircuitResult
  | [] => ([], acc)
  | ws :: wss =>
    let cl := seqExactlyOneClause n base ws
    let nextAcc := n + base + cl.gates.length
    let rest := seqExactlyOneFold n (base + cl.gates.length + 1) nextAcc wss
    (cl.gates ++ [(.and, [acc, cl.outWire])] ++ rest.gates, rest.outWire)

/-- **Linear-size sequential exact-one De Morgan circuit** checking that every list `ws ∈ wss`
has precisely one `true` input wire among `0, …, n - 1`. Uses at most
`1 + 4 * wss.length + 3 * (wss.map List.length).sum` gates. -/
@[expose] def seqExactlyOneAll (n : ℕ) (wss : List (List ℕ)) : ExactOneCircuitResult :=
  let fold := seqExactlyOneFold n 1 n wss
  ((.const true, []) :: fold.gates, fold.outWire)

@[simp]
theorem length_seqExactlyOneFold (n base acc : ℕ) (wss : List (List ℕ)) :
    (seqExactlyOneFold n base acc wss).gates.length =
      4 * wss.length + 3 * (wss.map List.length).sum := by
  induction wss generalizing base acc with
  | nil => simp [seqExactlyOneFold]
  | cons ws wss ih =>
    simp only [seqExactlyOneFold, List.length_append, List.length_cons, List.length_nil,
      length_seqExactlyOneClause, ih, List.map_cons, List.sum_cons]
    omega

@[simp]
theorem length_seqExactlyOneAll (n : ℕ) (wss : List (List ℕ)) :
    (seqExactlyOneAll n wss).gates.length =
      1 + 4 * wss.length + 3 * (wss.map List.length).sum := by
  simp only [seqExactlyOneAll, List.length_cons, length_seqExactlyOneFold]
  omega

private theorem isCodeFrom_seqExactlyOneFold (n : ℕ) :
    ∀ (wss : List (List ℕ)) (base acc : ℕ),
      (∀ ws ∈ wss, ∀ w ∈ ws, w < n + base) → acc < n + base →
        Program.IsCodeFrom signature n base (seqExactlyOneFold n base acc wss).gates ∧
        (seqExactlyOneFold n base acc wss).outWire <
          n + (base + (seqExactlyOneFold n base acc wss).gates.length)
  | [], _, acc, _, hacc => by
    simp only [seqExactlyOneFold, List.length_nil, Nat.add_zero]
    exact ⟨trivial, hacc⟩
  | ws :: wss, base, acc, hwss, hacc => by
    have hcl := isCodeFrom_seqExactlyOneClause n base (hwss ws (List.mem_cons_self ..))
    have hsnd : (seqExactlyOneClause n base ws).outWire <
        n + (base + (seqExactlyOneClause n base ws).gates.length) := by
      rw [snd_seqExactlyOneClause, length_seqExactlyOneClause]; omega
    have hrest := isCodeFrom_seqExactlyOneFold n wss
      (base + (seqExactlyOneClause n base ws).gates.length + 1)
      (n + base + (seqExactlyOneClause n base ws).gates.length)
      (fun ws' hws' w hw => (hwss ws' (List.mem_cons_of_mem _ hws') w hw).trans (by omega))
      (by omega)
    dsimp only [seqExactlyOneFold]
    rw [List.append_assoc, Program.isCodeFrom_append]
    refine ⟨⟨hcl, ?_⟩, ?_⟩
    · refine isCodeFrom_bin n (base + (seqExactlyOneClause n base ws).gates.length) .and rfl
        acc (seqExactlyOneClause n base ws).outWire _ (by omega)
        (hsnd.trans_eq (by omega)) ?_
      have hrest' : Program.IsCodeFrom signature n
          (base + ((seqExactlyOneClause n base ws).gates.length + 1))
          (seqExactlyOneFold n (base + (seqExactlyOneClause n base ws).gates.length + 1)
            (n + base + (seqExactlyOneClause n base ws).gates.length) wss).1 := by
        simpa only [Nat.add_assoc] using hrest.gates
      exact hrest'
    · simp only [List.length_append, List.length_cons, List.length_nil]
      have := hrest.outWire
      omega

/-- `seqExactlyOneAll n wss` is a well-formed De Morgan gate list on `n` inputs whenever every
wire in every list of `wss` is `< n`. -/
theorem isCodeFrom_seqExactlyOneAll (n : ℕ) {wss : List (List ℕ)}
    (hwss : ∀ ws ∈ wss, ∀ w ∈ ws, w < n) :
    Program.IsCodeFrom signature n 0 (seqExactlyOneAll n wss).gates := by
  have hfold := isCodeFrom_seqExactlyOneFold n wss 1 n
    (fun ws hws w hw => (hwss ws hws w hw).trans (by omega)) (by omega)
  exact isCodeFrom_const n 0 true _ hfold.gates

/-- The output wire of `seqExactlyOneAll n wss` lies strictly below `n + gates.length`. -/
theorem snd_lt_seqExactlyOneAll (n : ℕ) {wss : List (List ℕ)}
    (hwss : ∀ ws ∈ wss, ∀ w ∈ ws, w < n) :
    (seqExactlyOneAll n wss).outWire < n + (seqExactlyOneAll n wss).gates.length := by
  have hfold := isCodeFrom_seqExactlyOneFold n wss 1 n
    (fun ws hws w hw => (hwss ws hws w hw).trans (by omega)) (by omega)
  simp only [seqExactlyOneAll, List.length_cons]
  have := hfold.outWire
  omega

private theorem evalCode_seqExactlyOneFold (x : List Bool) (prefixGates : List (Op × List ℕ))
    (acc : ℕ) (wss : List (List ℕ))
    (hwss : ∀ ws ∈ wss, ∀ w ∈ ws, w < x.length + prefixGates.length)
    (hacc : acc < x.length + prefixGates.length) :
    let fold := seqExactlyOneFold x.length prefixGates.length acc wss
    let vals := evalCode interpretation false x (prefixGates ++ fold.gates)
    vals.getD fold.outWire false =
      ((evalCode interpretation false x prefixGates).getD acc false &&
        wss.all fun ws => decide (ws.countP (fun w =>
          (evalCode interpretation false x prefixGates).getD w false) = 1)) := by
  induction wss generalizing prefixGates acc with
  | nil => simp [seqExactlyOneFold]
  | cons ws wss ih =>
    let k := prefixGates.length
    let cl := seqExactlyOneClause x.length k ws
    let nextAcc := x.length + k + cl.gates.length
    let prefixCl := prefixGates ++ cl.gates
    let prefixNext := prefixCl ++ [(.and, [acc, cl.outWire])]
    have hclEval := evalCode_seqExactlyOneClause x prefixGates ws (hwss ws (List.mem_cons_self ..))
    have hreadCl_acc : (evalCode interpretation false x prefixCl).getD acc false =
        (evalCode interpretation false x prefixGates).getD acc false :=
      getD_evalCode_prefix hacc
    have hnextAcc : (evalCode interpretation false x prefixNext).getD nextAcc false =
        ((evalCode interpretation false x prefixGates).getD acc false &&
          decide (ws.countP (fun w =>
            (evalCode interpretation false x prefixGates).getD w false) = 1)) := by
      dsimp only [prefixNext, nextAcc]
      have hlenCl : x.length + k + cl.gates.length = x.length + prefixCl.length := by
        dsimp only [prefixCl, k]
        rw [List.length_append]
        omega
      rw [hlenCl, getD_evalCode_append_bin, Op.value, hreadCl_acc, hclEval]
    have hreadNext (u : ℕ) (hu : u < x.length + k) :
        (evalCode interpretation false x prefixNext).getD u false =
          (evalCode interpretation false x prefixGates).getD u false := by
      have hu' : u < x.length + prefixCl.length := by simp [prefixCl]; omega
      rw [show prefixNext = prefixCl ++ [(.and, [acc, cl.outWire])] from rfl,
        getD_evalCode_prefix hu', getD_evalCode_prefix hu]
    have hlenNext : prefixNext.length = k + cl.gates.length + 1 := by
      dsimp only [prefixNext, prefixCl, k]
      rw [List.length_append, List.length_append, List.length_singleton]
    have hih := ih prefixNext nextAcc
      (fun ws' hws' w hw => (hwss ws' (List.mem_cons_of_mem _ hws') w hw).trans (by omega))
      (by omega)
    rw [hlenNext] at hih
    have hassoc : prefixNext ++ (seqExactlyOneFold x.length (k + cl.gates.length + 1) nextAcc wss).1 =
        prefixGates ++ (seqExactlyOneFold x.length k acc (ws :: wss)).1 := by
      simp [prefixNext, prefixCl, seqExactlyOneFold, cl, nextAcc, List.append_assoc]
    change _ at hih
    dsimp only at hih ⊢
    change (evalCode interpretation false x
      (prefixGates ++ (seqExactlyOneFold x.length k acc (ws :: wss)).1)).getD
        (seqExactlyOneFold x.length k acc (ws :: wss)).2 false = _
    have hsnd : (seqExactlyOneFold x.length k acc (ws :: wss)).2 =
        (seqExactlyOneFold x.length (k + cl.gates.length + 1) nextAcc wss).2 := rfl
    rw [hsnd, ← hassoc, hih, hnextAcc]
    have hall :
        (wss.all fun ws' => decide (ws'.countP (fun w =>
          (evalCode interpretation false x prefixNext).getD w false) = 1)) =
        (wss.all fun ws' => decide (ws'.countP (fun w =>
          (evalCode interpretation false x prefixGates).getD w false) = 1)) := by
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      refine forall₂_congr fun ws' hws' => ?_
      have hcnt : ws'.countP (fun w => (evalCode interpretation false x prefixNext).getD w false) =
          ws'.countP (fun w => (evalCode interpretation false x prefixGates).getD w false) := by
        refine List.countP_congr fun w hw => ?_
        rw [hreadNext w (hwss ws' (List.mem_cons_of_mem _ hws') w hw)]
      rw [hcnt]
    rw [hall]
    simp [List.all_cons, Bool.and_assoc]

/-- **Evaluation correctness of `seqExactlyOneAll`**: `evalOutput x gates out` holds iff every
list `ws ∈ wss` contains precisely one wire where `x` evaluates to `true`. -/
theorem evalOutput_seqExactlyOneAll (x : List Bool) {wss : List (List ℕ)}
    (hwss : ∀ ws ∈ wss, ∀ w ∈ ws, w < x.length) :
    let res := seqExactlyOneAll x.length wss
    evalOutput x res.gates res.outWire =
      wss.all fun ws => decide (ws.countP (fun w => x.getD w false) = 1) := by
  let prefix1 : List (Op × List ℕ) := [(.const true, [])]
  have h1 : (evalCode interpretation false x prefix1).getD x.length false = true := by
    have h0 := getD_evalCode_append_const (x := x) (gates := []) true
    simpa [prefix1] using h0
  have hfold := evalCode_seqExactlyOneFold x prefix1 x.length wss
    (fun ws hws w hw => (hwss ws hws w hw).trans (by simp [prefix1])) (by simp [prefix1])
  have hread (w : ℕ) (hw : w < x.length) :
      (evalCode interpretation false x prefix1).getD w false = x.getD w false :=
    getD_evalCode_prefix (gates := []) (rest := prefix1) hw
  simp only [prefix1, List.length_singleton] at hfold
  change (evalCode interpretation false x ([(.const true, [])] ++
    (seqExactlyOneFold x.length 1 x.length wss).gates)).getD
      (seqExactlyOneFold x.length 1 x.length wss).outWire false = _ at hfold
  unfold evalOutput
  change (evalCode interpretation false x ([(.const true, [])] ++
    (seqExactlyOneFold x.length 1 x.length wss).gates)).getD
      (seqExactlyOneFold x.length 1 x.length wss).outWire false = _
  rw [hfold, h1, Bool.true_and, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun ws hws => ?_
  have hcnt : ws.countP (fun w => (evalCode interpretation false x prefix1).getD w false) =
      ws.countP (fun w => x.getD w false) := by
    refine List.countP_congr fun w hw => ?_
    rw [hread w (hwss ws hws w hw)]
  rw [hcnt]

end Cslib.Circuits.Boolean
