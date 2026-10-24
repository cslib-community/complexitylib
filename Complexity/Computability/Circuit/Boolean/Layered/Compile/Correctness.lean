/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered.Compile
import Mathlib.Data.List.GetD

/-!
# Correctness of depth-bounded Boolean circuit compilation

After the two microlevels for depth `k`, every original wire of depth at most `k` is available
at its original position and has its original value. Deeper gates may remain placeholders.
This invariant covers unused gates and the input-only initial row.

## Main results

* `Cslib.Circuits.Boolean.Layered.getD_eval_schedule`: every ready wire has its original value.
* `Cslib.Circuits.Boolean.Layered.wellFormed_compile`: every scheduled reference is valid.
* `Cslib.Circuits.Boolean.Layered.outputs_valid_compile`: output indices address the final row.
* `Cslib.Circuits.Boolean.Layered.select_eval_compile`: the ordered outputs equal the original
  circuit evaluation, including depth-zero wiring and repeated outputs.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

variable {n g m : ℕ}

private theorem valid_prepareFirst (line : Line signature n g) {width : ℕ}
    (h : ∀ a, (line.wires a).toNat < width) : (prepareFirst line.code).Valid width := by
  rcases line with ⟨op, wires⟩
  cases op <;> simp_all [prepareFirst, Line.code, Node.Valid]

private theorem valid_prepareSecond (line : Line signature n g) {width : ℕ}
    (h : ∀ a, (line.wires a).toNat < width) : (prepareSecond line.code).Valid width := by
  rcases line with ⟨op, wires⟩
  cases op <;> simp_all [prepareSecond, Line.code, Node.Valid]

private theorem valid_finish (inputCount gateCount : ℕ) {j : ℕ} (hj : j < gateCount)
    (op : Op) : (finish inputCount gateCount j op).Valid (inputCount + 3 * gateCount) := by
  cases op <;> simp only [finish, Node.Valid] <;> omega

private theorem valid_prepareLayer (p : Program signature n g) (k width : ℕ)
    (hready : ∀ w : Wire n g, p.wireDepths w ≤ k → w.toNat < width) :
    ∀ node ∈ prepareLayer n p.code (wireDepthsCode n p.code) (k + 1), node.Valid width := by
  have hargs (j : ℕ) (hj : j < p.code.length)
      (hlevel : (wireDepthsCode n p.code).getD (n + j) 0 = k + 1) :
      ∀ a, ((p.lines ⟨j, hj.trans_eq p.length_code⟩).wires a).toNat < width := by
    let index : Fin g := ⟨j, hj.trans_eq p.length_code⟩
    have hdepth := wireDepthsCode_getD_toNat p (.gate index)
    change (wireDepthsCode n p.code).getD (n + j) 0 = p.depths index at hdepth
    intro a
    apply hready
    exact Nat.le_of_lt_succ ((p.wireDepths_lines_lt index a).trans_eq
      (hdepth.symm.trans hlevel))
  intro node hnode
  simp only [prepareLayer, List.mem_append, List.mem_map, List.mem_range] at hnode
  rcases hnode with (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
  · unfold carry
    split_ifs with h
    · let w : Wire n g := Wire.ofNat i (hi.trans_eq (congrArg (n + ·) p.length_code))
      have hdepth := wireDepthsCode_getD_toNat p w
      simp only [w, Wire.toNat_ofNat] at hdepth
      have := hready w (Nat.le_of_lt_succ (hdepth ▸ h))
      simpa only [Node.Valid, w, Wire.toNat_ofNat] using this
    · trivial
  · split_ifs with h
    · rw [Program.getD_code p ⟨j, hj.trans_eq p.length_code⟩ (.const false, [])]
      exact valid_prepareFirst _ (hargs j hj h)
    · trivial
  · split_ifs with h
    · rw [Program.getD_code p ⟨j, hj.trans_eq p.length_code⟩ (.const false, [])]
      exact valid_prepareSecond _ (hargs j hj h)
    · trivial

private theorem valid_finishLayer (inputCount : ℕ) (gates : List (Op × List ℕ))
    (depths : List ℕ) (level : ℕ) :
    ∀ node ∈ finishLayer inputCount gates depths level,
      node.Valid (inputCount + 3 * gates.length) := by
  intro node hnode
  simp only [finishLayer, List.mem_append, List.mem_map, List.mem_range,
    List.mem_replicate] at hnode
  rcases hnode with (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨_, rfl⟩
  · change i < inputCount + 3 * gates.length
    omega
  · split_ifs with h
    · exact valid_finish _ _ hj _
    · unfold carry
      split_ifs
      · simp only [Node.Valid]
        omega
      · trivial
  · trivial

private theorem eval_round (p : Program signature n g) (x : Fin n → Bool)
    (k : ℕ) (inputs : List Bool)
    (hvalues : ∀ w : Wire n g, p.wireDepths w ≤ k →
      inputs.getD w.toNat false = p.trace interpretation x w) :
    ∀ w : Wire n g, p.wireDepths w ≤ k + 1 →
      (evalLayer (evalLayer inputs (prepareLayer n p.code (wireDepthsCode n p.code) (k + 1)))
        (finishLayer n p.code (wireDepthsCode n p.code) (k + 1))).getD w.toNat false =
          p.trace interpretation x w := by
  intro w hw
  cases w with
  | input i =>
    rw [Wire.toNat_input, getD_eval_finishLayer_input _ _ _ _ _ i.isLt,
      getD_eval_prepareLayer_main _ _ _ _ _ (by omega)]
    have hdepth := wireDepthsCode_getD_toNat p (.input i)
    change (wireDepthsCode n p.code).getD i 0 = 0 at hdepth
    rw [carry, hdepth, ite_eq_left (by omega), Node.eval]
    exact hvalues (.input i) (Nat.zero_le _)
  | gate j =>
    have hj : j.val < p.code.length := j.isLt.trans_eq p.length_code.symm
    have hdepth := wireDepthsCode_getD_toNat p (.gate j)
    change (wireDepthsCode n p.code).getD (n + j.val) 0 = p.depths j at hdepth
    change p.depths j ≤ k + 1 at hw
    rw [Wire.toNat_gate, getD_eval_finishLayer_gate _ _ _ _ _ hj, hdepth]
    by_cases hactive : p.depths j = k + 1
    · rw [ite_eq_left hactive, Program.getD_code p j (.const false, []), Line.code_fst]
      rw [finish_prepare_eq _ _ _ _ hj (p.lines j)
        (Program.getD_code p j (.const false, [])) (hdepth.trans hactive)]
      have hargs : (fun a => inputs.getD ((p.lines j).wires a).toNat false) =
          (fun a => p.trace interpretation x ((p.lines j).wires a)) := by
        funext a
        apply hvalues
        exact Nat.le_of_lt_succ ((p.wireDepths_lines_lt j a).trans_eq hactive)
      rw [hargs]
      exact p.lines_eval interpretation x j
    · have hlt : p.depths j < k + 1 := by omega
      rw [ite_eq_right hactive, carry, hdepth, ite_eq_left hlt, Node.eval,
        getD_eval_prepareLayer_main _ _ _ _ _ (by omega), carry, hdepth,
        ite_eq_left hlt, Node.eval]
      exact hvalues (.gate j) (Nat.le_of_lt_succ hlt)

/-- Once a positive number of rounds has run, the row has the full working width. -/
theorem length_eval_schedule (inputs : List Bool) (inputCount : ℕ)
    (gates : List (Op × List ℕ)) (depths : List ℕ) (k : ℕ) :
    (eval inputs (schedule inputCount gates depths (k + 1))).length =
      inputCount + 3 * gates.length := by
  rw [schedule_succ, eval_append]
  simp only [eval_cons, eval_nil, length_evalLayer, length_finishLayer]

private theorem schedule_correct (p : Program signature n g) (x : Fin n → Bool) (k : ℕ) :
    WellFormed n (schedule n p.code (wireDepthsCode n p.code) k) ∧
      ∀ w : Wire n g, p.wireDepths w ≤ k →
        w.toNat < (eval (List.ofFn x) (schedule n p.code (wireDepthsCode n p.code) k)).length ∧
        (eval (List.ofFn x) (schedule n p.code (wireDepthsCode n p.code) k)).getD w.toNat false =
          p.trace interpretation x w := by
  induction k with
  | zero =>
    refine ⟨trivial, fun w hw => ?_⟩
    cases w with
    | input i => simp [schedule_zero, eval_nil, Wire.toNat_input, Program.trace_input]
    | gate j =>
      have := p.depths_pos j
      change p.depths j ≤ 0 at hw
      omega
  | succ k ih =>
    have hprepare := valid_prepareLayer p k _ (fun w hw => (ih.2 w hw).1)
    have hfinish := valid_finishLayer n p.code (wireDepthsCode n p.code) (k + 1)
    have hvalues := eval_round p x k _ (fun w hw => (ih.2 w hw).2)
    refine ⟨?_, fun w hw => ⟨?_, ?_⟩⟩
    · rw [schedule_succ, wellFormed_append]
      refine ⟨ih.1, ?_⟩
      simpa only [wellFormed_cons, wellFormed_nil, and_true, length_prepareLayer,
        length_eval, List.length_ofFn] using And.intro hprepare hfinish
    · rw [length_eval_schedule]
      have := w.toNat_lt
      have := p.length_code
      omega
    · rw [schedule_succ, eval_append, eval_cons, eval_cons, eval_nil]
      exact hvalues w hw

/-- Every compiled reference reads an available preceding-layer wire, including at depth zero. -/
private theorem wellFormed_schedule (p : Program signature n g) (k : ℕ) :
    WellFormed n (schedule n p.code (wireDepthsCode n p.code) k) :=
  (schedule_correct p (fun _ => false) k).1

/-- Every original wire of depth at most the completed level is available at its original index. -/
theorem toNat_lt_length_eval_schedule (p : Program signature n g) (x : Fin n → Bool)
    (k : ℕ) (w : Wire n g) (hw : p.wireDepths w ≤ k) :
    w.toNat < (eval (List.ofFn x) (schedule n p.code (wireDepthsCode n p.code) k)).length :=
  ((schedule_correct p x k).2 w hw).1

/-- The schedule preserves each completed original wire's value; deeper unused gates need not
have been computed. -/
theorem getD_eval_schedule (p : Program signature n g) (x : Fin n → Bool) (k : ℕ)
    (w : Wire n g) (hw : p.wireDepths w ≤ k) :
    (eval (List.ofFn x) (schedule n p.code (wireDepthsCode n p.code) k)).getD w.toNat false =
      p.trace interpretation x w :=
  ((schedule_correct p x k).2 w hw).2

/-- The actual compiler produces a well-formed layered schedule for every typed circuit. -/
theorem wellFormed_compile (c : Circuit signature n m) : WellFormed n (compile n c.code).1 :=
  wellFormed_schedule c.program _

private theorem output_depth_le (c : Circuit signature n m) (j : Fin m) :
    c.program.wireDepths (c.outputs j) ≤ c.depth := by
  simpa only [Program.wireDepthsWith_one, Circuit.depthWith_one] using
    c.wireDepthsWith_outputs_le_depthWith 1 j

/-- All designated outputs select existing final wires. This also covers an empty schedule with
dead gates, whose available final wires are only the original inputs. -/
theorem outputs_valid_compile (c : Circuit signature n m) :
    ∀ i ∈ (compile n c.code).2, i < outputWidth n (compile n c.code).1 := by
  intro i hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hi
  have h := toNat_lt_length_eval_schedule c.program (fun _ => false) c.depth (c.outputs j)
    (output_depth_le c j)
  change (c.outputs j).toNat < outputWidth n
    (schedule n c.program.code (wireDepthsCode n c.program.code) (depthCode n c.code))
  rw [depthCode_code]
  simpa only [length_eval, List.length_ofFn] using h

/-- Compilation preserves every output's Boolean value, in order and with repetitions. -/
theorem select_eval_compile (c : Circuit signature n m) (x : Fin n → Bool) :
    select (eval (List.ofFn x) (compile n c.code).1) (compile n c.code).2 =
      List.ofFn (c.eval interpretation x) := by
  simp only [compile, depthCode_code]
  simp only [select, Circuit.code, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact getD_eval_schedule c.program x c.depth (c.outputs j) (output_depth_le c j)

end Cslib.Circuits.Boolean.Layered
