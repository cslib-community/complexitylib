/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (spike for #4383 M5.4d; not for merge)

public import CslibFrontier.Computability.Circuit.Boolean.Oracle
public import CslibFrontier.Computability.Circuit.Boolean.Comparison
public import CslibFrontier.Computability.Circuit.CompositionDepth
public import CslibFrontier.Computability.Circuit.FanIn
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Computability.Circuit.Simulation

/-!
# Spike: one selection round of an oracle circuit

Scratch for #4383 (M5.4d). Not for merge.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ τ : Signature} {n m g : ℕ}

/-- Translating operations composes the cost with the translation. -/
theorem Program.cost_mapOp (φ : σ.Hom τ) (p : Program σ n g) (cost : τ.Op → ℕ) :
    (p.mapOp φ).cost cost = p.cost (cost ∘ φ) := by
  induction p with
  | empty => rfl
  | gate p line ih => simp [ih]

/-- A program whose operations all cost zero has weighted depth zero at every gate. -/
theorem Program.depthsWith_eq_zero (cost : σ.Op → ℕ) (p : Program σ n g)
    (h : ∀ k, cost (p.lines k).op = 0) (k : Fin g) : p.depthsWith cost k = 0 :=
  Nat.eq_zero_of_le_zero <| (p.depthsWith_le_mul_depths (b := 0) (fun k => (h k).le) k).trans
    (by simp)

/-- A circuit whose operations all cost zero has weighted depth zero. -/
theorem Circuit.depthWith_eq_zero (cost : σ.Op → ℕ) (c : Circuit σ n m)
    (h : ∀ k, cost (c.program.lines k).op = 0) : c.depthWith cost = 0 :=
  Nat.eq_zero_of_le_zero <| (c.depthWith_le_mul_depth (b := 0) fun k => (h k).le).trans (by simp)

variable {p : ℕ}

@[simp] theorem Circuit.cost_comp (cost : σ.Op → ℕ) (d : Circuit σ m p) (c : Circuit σ n m) :
    (d.comp c).program.cost cost = c.program.cost cost + d.program.cost cost :=
  Program.cost_append _ _ _ _

@[simp] theorem Circuit.cost_append (cost : σ.Op → ℕ) (c : Circuit σ n m) (d : Circuit σ n p) :
    (c.append d).program.cost cost = c.program.cost cost + d.program.cost cost :=
  Program.cost_append _ _ _ _

@[simp] theorem Circuit.cost_wiring (cost : σ.Op → ℕ) (select : Fin m → Fin n) :
    (Circuit.wiring σ select).program.cost cost = 0 :=
  rfl

@[simp] theorem Circuit.cost_oneGate (cost : σ.Op → ℕ) (op : σ.Op) (args : Fin (σ.Arity op) → Fin n) :
    (Circuit.oneGate op args).program.cost cost = cost op :=
  Nat.zero_add _

@[simp] theorem Circuit.cost_pi (cost : σ.Op → ℕ) (cs : Fin m → Circuit σ n 1) :
    (Circuit.pi cs).program.cost cost = ∑ j, (cs j).program.cost cost := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Circuit.pi, Circuit.cost_append, ih, Fin.sum_univ_castSucc]

end Cslib.Circuits

namespace Cslib.Circuits.Boolean

variable {n m g : ℕ}

/-- The lines of a translated program are the translated lines. -/
theorem Program.lines_mapOp_op (p : Program signature n g) (k : Fin g) :
    ((p.mapOp toOracle).lines k).op = OracleOp.base (p.lines k).op := by
  induction p with
  | empty => exact k.elim0
  | gate p line ih =>
    induction k using Fin.lastCases with
    | last => simp [toOracle, DFunLike.coe]
    | cast k => simpa using ih k

/-- A De Morgan circuit, viewed in the oracle basis, has no oracle gates. -/
@[simp] theorem cost_mapOp_toOracle (c : Circuit signature n m) :
    (c.mapOp toOracle).program.cost OracleOp.queryWeight = 0 :=
  (Program.cost_mapOp toOracle c.program _).trans <|
    (c.program.cost_const 0).trans (Nat.zero_mul _)

/-- A De Morgan circuit, viewed in the oracle basis, has oracle depth zero. -/
@[simp] theorem depthWith_mapOp_toOracle (c : Circuit signature n m) :
    (c.mapOp toOracle).depthWith OracleOp.queryWeight = 0 :=
  Circuit.depthWith_eq_zero _ _ fun k =>
    (congrArg OracleOp.queryWeight (Program.lines_mapOp_op c.program k)).trans rfl

/-- Every De Morgan circuit has fan-in at most two. -/
theorem fanInAtMost_two (c : Circuit signature n m) : c.FanInAtMost 2 :=
  Program.fanInAtMost_iff.2 fun k => by
    rcases (c.program.lines k).op with _ | _ | _ | _ <;> simp

/-! ### Selecting the first accepted candidate -/

/-- The word of the first accepted candidate, or the default `d` when none is accepted. -/
def firstSel {w : ℕ} (d : BitString w) : {N : ℕ} → (Fin N → Bool) → (Fin N → BitString w) →
    BitString w
  | 0, _, _ => d
  | _ + 1, acc, word => if acc 0 then word 0 else firstSel d (acc ∘ Fin.succ) (word ∘ Fin.succ)

/-- The selected word is the default or one of the candidate words. -/
theorem firstSel_mem {w : ℕ} (d : BitString w) {N : ℕ} (acc : Fin N → Bool)
    (word : Fin N → BitString w) : firstSel d acc word = d ∨ ∃ i, firstSel d acc word = word i := by
  induction N with
  | zero => exact .inl rfl
  | succ N ih =>
    unfold firstSel
    split
    · exact .inr ⟨0, rfl⟩
    · rcases ih (acc ∘ Fin.succ) (word ∘ Fin.succ) with h | ⟨i, h⟩
      · exact .inl h
      · exact .inr ⟨i.succ, h⟩

/-- When some candidate is accepted, the selected word is that of an accepted candidate. -/
theorem firstSel_accepted {w : ℕ} (d : BitString w) {N : ℕ} (acc : Fin N → Bool)
    (word : Fin N → BitString w) (h : ∃ i, acc i = true) :
    ∃ i, acc i = true ∧ firstSel d acc word = word i := by
  induction N with
  | zero => exact absurd h (by simp)
  | succ N ih =>
    unfold firstSel
    split
    · exact ⟨0, by assumption, rfl⟩
    · rename_i h0
      obtain ⟨i, hi⟩ := h
      cases i using Fin.cases with
      | zero => exact absurd hi h0
      | succ i =>
        obtain ⟨j, hj, hsel⟩ := ih (acc ∘ Fin.succ) (word ∘ Fin.succ) ⟨i, hi⟩
        exact ⟨j.succ, hj, hsel⟩

/-- The De Morgan circuit selecting the first accepted candidate: candidate `i` is accepted when
input `acc i` is true, and its word is read from the inputs `word i`; the default word is read
from the inputs `dflt`. A chain of multiplexers. -/
def selectFirst {K w : ℕ} (dflt : Fin w → Fin K) :
    {N : ℕ} → (Fin N → Fin K) → (Fin N → Fin w → Fin K) → Circuit signature K w
  | 0, _, _ => Circuit.wiring signature dflt
  | _ + 1, acc, word =>
    (muxCircuit w).comp
      ((Circuit.wiring signature fun _ : Fin 1 => acc 0).append
        ((Circuit.wiring signature (word 0)).append
          (selectFirst dflt (acc ∘ Fin.succ) (word ∘ Fin.succ))))

@[simp] theorem eval_selectFirst {K w : ℕ} (dflt : Fin w → Fin K) {N : ℕ} (acc : Fin N → Fin K)
    (word : Fin N → Fin w → Fin K) (x : BitString K) :
    (selectFirst dflt acc word).eval interpretation x =
      firstSel (x ∘ dflt) (x ∘ acc) (fun i => x ∘ word i) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [selectFirst, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_append,
      Circuit.eval_wiring, Circuit.eval_wiring, ih]
    exact eval_muxCircuit (x (acc 0)) _ _

@[simp] theorem size_selectFirst {K w : ℕ} (dflt : Fin w → Fin K) {N : ℕ} (acc : Fin N → Fin K)
    (word : Fin N → Fin w → Fin K) : (selectFirst dflt acc word).size = N * (3 * w + 1) := by
  induction N with
  | zero => rw [Nat.zero_mul]; rfl
  | succ N ih =>
    rw [selectFirst, Circuit.size_comp, Circuit.size_append, Circuit.size_append,
      Circuit.size_wiring, Circuit.size_wiring, ih, size_muxCircuit]
    ring

/-! ### One round -/

/-- A wire source in a round: one of the `K` inputs, or a constant. -/
abbrev Source (K : ℕ) := Fin K ⊕ Bool

/-- The value of a source on the input `x`. -/
def Source.val {K : ℕ} (x : BitString K) : Source K → Bool
  | .inl i => x i
  | .inr b => b

/-- The wire carrying a source after the constant layer. -/
def Source.idx {K : ℕ} : Source K → Fin (K + 2)
  | .inl i => Fin.castAdd 2 i
  | .inr false => Fin.natAdd K (Fin.castAdd 1 (0 : Fin 1) : Fin (1 + 1))
  | .inr true => Fin.natAdd K (Fin.natAdd 1 (0 : Fin 1) : Fin (1 + 1))

/-- The inputs followed by the constants `false` and `true`. Two gates. -/
def constLayer (K : ℕ) : Circuit oracleSignature K (K + 2) :=
  (Circuit.id oracleSignature K).append
    ((Circuit.oneGate (σ := oracleSignature) (OracleOp.base (.const false)) Fin.elim0).append
      (Circuit.oneGate (σ := oracleSignature) (OracleOp.base (.const true)) Fin.elim0))

theorem eval_constLayer_idx {K : ℕ} (O : Language Bool) (x : BitString K) (s : Source K) :
    (constLayer K).eval (oracleInterpretation O) x s.idx = s.val x := by
  rcases s with i | _ | _
  · simp [constLayer, Source.idx, Source.val, Circuit.eval_append, Fin.append_left]
  all_goals
    simp only [constLayer, Source.idx, Source.val, Circuit.eval_append, Fin.append_right]
    rfl

@[simp] theorem size_constLayer (K : ℕ) : (constLayer K).size = 2 := rfl

@[simp] theorem cost_constLayer (K : ℕ) :
    (constLayer K).program.cost OracleOp.queryWeight = 0 := rfl

theorem depthWith_constLayer (K : ℕ) : (constLayer K).depthWith OracleOp.queryWeight = 0 :=
  Nat.eq_zero_of_le_zero <| (Circuit.depthWith_append_le _ _ _).trans <| max_le (by simp) <|
    (Circuit.depthWith_append_le _ _ _).trans <| max_le (by simp) (by simp)

theorem fanInAtMost_constLayer (K r : ℕ) : (constLayer K).FanInAtMost r :=
  (Circuit.fanInAtMost_wiring _ _).append <|
    ((Circuit.fanInAtMost_oneGate _ _ _).2 (Nat.zero_le _)).append
      ((Circuit.fanInAtMost_oneGate _ _ _).2 (Nat.zero_le _))

/-- `N` oracle gates side by side; gate `i` reads the `q` wires `src i` of the constant layer's
output. -/
def queryLayer {K N q : ℕ} (src : Fin N → Fin q → Source K) : Circuit oracleSignature (K + 2) N :=
  Circuit.pi fun i => Circuit.oneGate (σ := oracleSignature) (OracleOp.query q)
    fun a => (src i a).idx

@[simp] theorem eval_queryLayer {K N q : ℕ} (src : Fin N → Fin q → Source K) (O : Language Bool)
    (x : BitString K) (i : Fin N) :
    (queryLayer src).eval (oracleInterpretation O) ((constLayer K).eval (oracleInterpretation O) x) i =
      O.slice q fun a => (src i a).val x := by
  simp [queryLayer, eval_constLayer_idx]

@[simp] theorem size_queryLayer {K N q : ℕ} (src : Fin N → Fin q → Source K) :
    (queryLayer src).size = N := by
  simp [queryLayer]

@[simp] theorem cost_queryLayer {K N q : ℕ} (src : Fin N → Fin q → Source K) :
    (queryLayer src).program.cost OracleOp.queryWeight = N := by
  simp only [queryLayer, Circuit.cost_pi, Circuit.cost_oneGate, OracleOp.queryWeight_query,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem depthWith_queryLayer_le {K N q : ℕ} (src : Fin N → Fin q → Source K) :
    (queryLayer src).depthWith OracleOp.queryWeight ≤ 1 :=
  Circuit.depthWith_pi_le _ _ fun _ => by simp

theorem fanInAtMost_queryLayer {K N q : ℕ} (src : Fin N → Fin q → Source K) :
    (queryLayer src).FanInAtMost q :=
  Circuit.fanInAtMost_pi fun _ => (Circuit.fanInAtMost_oneGate _ _ _).2 le_rfl

end Cslib.Circuits.Boolean
