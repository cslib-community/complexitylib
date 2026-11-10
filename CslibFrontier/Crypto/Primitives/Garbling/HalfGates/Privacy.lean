/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Primitives.Garbling.CorrelationRobust
public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.Tabulate
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Probability.Uniform

/-!
# Privacy of half-gates garbling

The evaluator of a half-gates garbled circuit sees a `View`: the two ciphertexts of each AND gate,
one label per input wire and the output decoding bits. Privacy in the simulation sense of
[ZahurRosulekEvans2015] asks for a simulator that produces an indistinguishable view from the
circuit and its output alone. The simulator `simulate` samples uniform input labels and a uniform
table, and sets the decoding bits so that the evaluated output labels decode to the output.

Security rests on *circular correlation robustness* of the hash `H` [ZahurRosulekEvans2015]: for
a uniform offset `Δ = (R, true)`, the oracle `(a, t, b) ↦ H(a + Δ, t) + bΔ`
(`CorrelationRobust.circularLabel`) must be indistinguishable from a random function by
adversaries that never query both `(a, t, 0)` and `(a, t, 1)`. The assumption is the whole-label
form of the one in `Cslib.Crypto.Garbling.CorrelationRobust`, which Free-XOR uses with a hash that
reads only the key. It is phrased as the PRF game for the keyed function
`CorrelationRobust.circularLabel H` with key `R` (`CorrelationRobust.advantageLabel`).

The main theorem `advantage_realGame_simGame` states that the advantage of every distinguisher
`D` between the real and the simulated view, for a circuit `C` and an input `x`, *equals* the
advantage `CorrelationRobust.advantageLabel H` of an explicit reduction `reduction C H tw x D`,
provided the
tweaks of distinct slots are distinct. The reduction knows `x`, so it knows the bit `v_w` every
wire carries; it samples the input labels the evaluator holds and builds the table gate by gate
in wire order. For an AND gate whose arguments carry labels `A_a`, `A_b` it queries
`(A_a, t, p_b)` for the generator half, where `p_b = col(A_b) + v_b` is the colour of the zero
label of `b`, and `(A_b, t', v_a)` for the evaluator half, and adds the parts of the two
ciphertexts the evaluator can compute itself (`slotKnown`). With the CCR oracle this is the real
table, by the half-gates identity; with a random function every query has a distinct tweak, so
the table is uniform. Each slot is queried exactly once, at its own tweak, so the reduction never
queries both `(a, t, 0)` and `(a, t, 1)`; that legality condition is not formalized.

This is the single-instance form of simulation privacy: the circuit, the input and the
distinguisher are fixed, and the simulator receives the whole circuit `C`, the side information
`Φ(C)` of [ZahurRosulekEvans2015]. Running time is not tracked.

## Main definitions

* `Cslib.Crypto.Garbling.HalfGates.View`: what the evaluator sees.
* `Cslib.Crypto.Garbling.HalfGates.simulateWith`, `Cslib.Crypto.Garbling.HalfGates.simulate`: the
  simulator.
* `Cslib.Crypto.Garbling.HalfGates.realGame`, `Cslib.Crypto.Garbling.HalfGates.simGame`: the
  privacy experiments.
* `Cslib.Crypto.Garbling.HalfGates.reduction`: the CCR adversary.

## Main results

* `Cslib.Crypto.Garbling.HalfGates.View.run_simulateWith`: simulated views decode to the output.
* `Cslib.Crypto.Garbling.HalfGates.map_oracleTable`: against a random function the reduction's
  table is uniform.
* `Cslib.Crypto.Garbling.HalfGates.advantage_realGame_simGame`: privacy, as an equality with the
  CCR advantage of the reduction.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
-/

public section

namespace Cslib.Crypto.Garbling.HalfGates

open Cslib.Circuits Probability
open Cslib.Crypto.Garbling.CorrelationRobust (circularLabel advantageLabel)

variable {n m : ℕ} (C : Circuit signature n m) {K T : Type}

/-- What the evaluator of a half-gates garbled circuit sees: the garbled table, one label per
input wire and the output decoding bits. The circuit is public, as an index of the type. -/
@[ext] structure View (K : Type) where
  /-- The garbled table. -/
  table : Slot C → K × Bool
  /-- The label of each input wire. -/
  input : Fin n → K × Bool
  /-- The decoding bit of each output wire. -/
  decoding : Fin m → Bool

/-- The view of a garbled circuit on an input. -/
@[expose] def Garbled.view {C : Circuit signature n m} (G : Garbled C K) (x : Fin n → Bool) :
    View C K where
  table := G.table
  input i := G.encoding i (x i)
  decoding := G.decoding

variable [AddCommGroup K]

/-- Evaluate a view and decode the result. -/
@[expose] def View.run {C : Circuit signature n m} (V : View C K) (H : K × Bool → T → K × Bool)
    (tw : Slot C → T) : Fin m → Bool :=
  fun o => (evaluate C H tw V.table V.input o).2 + V.decoding o

/-- Running the view of a garbled circuit on `x` is running the garbled circuit on `x`. -/
theorem Garbled.run_view {C : Circuit signature n m} (G : Garbled C K)
    (H : K × Bool → T → K × Bool) (tw : Slot C → T) (x : Fin n → Bool) :
    (G.view x).run H tw = G.run H tw x := rfl

/-- The simulated view for input labels `X` and table `ct`: the decoding bits make the evaluated
output labels decode to `y`. -/
@[expose] def simulateWith (H : K × Bool → T → K × Bool) (tw : Slot C → T) (y : Fin m → Bool)
    (X : Fin n → K × Bool) (ct : Slot C → K × Bool) : View C K where
  table := ct
  input := X
  decoding o := (evaluate C H tw ct X o).2 + y o

/-- **Simulator correctness**: every simulated view decodes to `y`. -/
theorem View.run_simulateWith (H : K × Bool → T → K × Bool) (tw : Slot C → T) (y : Fin m → Bool)
    (X : Fin n → K × Bool) (ct : Slot C → K × Bool) :
    (simulateWith C H tw y X ct).run H tw = y := by
  funext o
  simp only [View.run, simulateWith]
  rw [← add_assoc, BooleanRing.add_self, zero_add]

/-- The circular correlation robustness oracle with offset key `R` in this file's notation: on
`(a, t, b)` it returns `H(a + Δ, t) + bΔ` for `Δ = offset R`. -/
private theorem circularLabel_eq (H : K × Bool → T → K × Bool) (R : K)
    (q : (K × Bool) × T × Bool) :
    circularLabel H R q = H (q.1 + offset R) q.2.1 + sel q.2.2 (offset R) := by
  obtain ⟨a, t, b⟩ := q
  rw [CorrelationRobust.circularLabel_apply]
  rfl

/-! ### The reduction's table -/

section Oracle

variable (H : K × Bool → T → K × Bool) (tw : Slot C → T) (x : Fin n → Bool)

/-- The CCR query for a slot, from the labels `E` the evaluator holds on input `x`: `(A_a, t, p_b)`
for the generator half and `(A_b, t', v_a)` for the evaluator half. -/
@[expose] def slotQuery (E : Wire n C.size → K × Bool) (s : Slot C) : (K × Bool) × T × Bool :=
  if s.2 then (E (right C s.1.1), tw s, C.program.trace interpretation x (left C s.1.1))
  else (E (left C s.1.1), tw s,
    (E (right C s.1.1)).2 + C.program.trace interpretation x (right C s.1.1))

/-- The part of a slot's ciphertext the evaluator computes from its own labels: `H(A_a, t)` for
the generator half and `H(A_b, t') + A_a` for the evaluator half. -/
@[expose] def slotKnown (E : Wire n C.size → K × Bool) (s : Slot C) : K × Bool :=
  if s.2 then H (E (right C s.1.1)) (tw s) + E (left C s.1.1) else H (E (left C s.1.1)) (tw s)

/-- The reduction's ciphertext for a slot, with oracle `f`, from the labels `E`. -/
@[expose] def entry (f : (K × Bool) × T × Bool → K × Bool) (E : Wire n C.size → K × Bool)
    (s : Slot C) : K × Bool :=
  slotKnown C H tw E s + f (slotQuery C tw x E s)

omit [AddCommGroup K] in
theorem slotQuery_snd_fst (E : Wire n C.size → K × Bool) (s : Slot C) :
    (slotQuery C tw x E s).2.1 = tw s := by
  unfold slotQuery
  split <;> rfl

omit [AddCommGroup K] in
theorem slotQuery_injective (htw : Function.Injective tw) (E : Wire n C.size → K × Bool) :
    Function.Injective (slotQuery C tw x E) := fun s s' h =>
  htw (by rw [← slotQuery_snd_fst C tw x E s, h, slotQuery_snd_fst])

theorem entry_congr (f : (K × Bool) × T × Bool → K × Bool) {E E' : Wire n C.size → K × Bool}
    (s : Slot C) (hl : E (left C s.1.1) = E' (left C s.1.1))
    (hr : E (right C s.1.1) = E' (right C s.1.1)) :
    entry C H tw x f E s = entry C H tw x f E' s := by
  simp only [entry, slotKnown, slotQuery, hl, hr]

theorem isLocal_entry (f : (K × Bool) × T × Bool → K × Bool) (X : Fin n → K × Bool) :
    IsLocal fun E => evalStep C H tw (entry C H tw x f E) X E :=
  isLocal_evalStep C H tw _ X fun _ _ p hl hr => entry_congr C H tw x f p hl hr

/-- The labels the evaluator holds when every ciphertext is the reduction's entry. -/
@[expose] def oracleLabels (f : (K × Bool) × T × Bool → K × Bool) (X : Fin n → K × Bool) :
    Wire n C.size → K × Bool :=
  (fun E => evalStep C H tw (entry C H tw x f E) X E)^[n + C.size] 0

/-- The reduction's table with oracle `f` and input labels `X`. -/
@[expose] def oracleTable (f : (K × Bool) × T × Bool → K × Bool) (X : Fin n → K × Bool) :
    Slot C → K × Bool :=
  entry C H tw x f (oracleLabels C H tw x f X)

theorem evalLabels_oracleTable (f : (K × Bool) × T × Bool → K × Bool) (X : Fin n → K × Bool) :
    evalLabels C H tw (oracleTable C H tw x f X) X = oracleLabels C H tw x f X :=
  (isLocal_evalStep_const C H tw _ X).iterate_eq_of_isFixed 0
    ((isLocal_entry C H tw x f X).isFixed_iterate 0)

/-- Tables agreeing on the gates below `k` give the same labels on the wires below `n + k`. -/
theorem evalLabels_congr (X : Fin n → K × Bool) {ct ct' : Slot C → K × Bool} (k : ℕ)
    (hct : ∀ s : Slot C, (s.1.1 : ℕ) < k → ct s = ct' s) (w : Wire n C.size)
    (hw : w.toNat < n + k) : evalLabels C H tw ct X w = evalLabels C H tw ct' X w := by
  have hE : evalStep C H tw ct X (evalLabels C H tw ct X) = evalLabels C H tw ct X :=
    (isLocal_evalStep_const C H tw ct X).isFixed_iterate 0
  have hE' : evalStep C H tw ct' X (evalLabels C H tw ct' X) = evalLabels C H tw ct' X :=
    (isLocal_evalStep_const C H tw ct' X).isFixed_iterate 0
  have key : ∀ N (w : Wire n C.size), w.toNat < N → w.toNat < n + k →
      evalLabels C H tw ct X w = evalLabels C H tw ct' X w := by
    intro N
    induction N with
    | zero => intro w hw; exact absurd hw (Nat.not_lt_zero _)
    | succ N ih =>
      intro w hN hk
      rw [← hE, ← hE']
      cases w with
      | input i => rfl
      | gate g =>
        rw [Wire.toNat_gate] at hN hk
        have hl := toNat_left_lt C g
        have hr := toNat_right_lt C g
        exact evalStep_gate_congr C H tw X g (fun h b => hct _ (by dsimp only; omega))
          (ih _ (by omega) (by omega)) (ih _ (by omega) (by omega))
  exact key _ w (Nat.lt_succ_self _) hw

/-- **Against a fixed function** the reduction's table is `oracleTable`: the fibre of a table
`ct` is the set of functions taking the prescribed values at the queries made from the labels
`ct` itself gives the evaluator. -/
theorem oracleTable_eq_iff (f : (K × Bool) × T × Bool → K × Bool) (X : Fin n → K × Bool)
    (ct : Slot C → K × Bool) :
    oracleTable C H tw x f X = ct ↔ (fun s => f (slotQuery C tw x (evalLabels C H tw ct X) s)) =
      fun s => ct s - slotKnown C H tw (evalLabels C H tw ct X) s := by
  constructor
  · rintro rfl
    funext s
    rw [evalLabels_oracleTable, oracleTable, entry, add_sub_cancel_left]
  · intro hf
    have hent : entry C H tw x f (evalLabels C H tw ct X) = ct :=
      funext fun s => by rw [entry, congrFun hf s, add_sub_cancel]
    have hL : oracleLabels C H tw x f X = evalLabels C H tw ct X :=
      (isLocal_entry C H tw x f X).iterate_eq_of_isFixed 0 (by
        rw [hent]
        exact (isLocal_evalStep_const C H tw ct X).isFixed_iterate 0)
    rw [oracleTable, hL, hent]

end Oracle

/-! ### The real table -/

section Real

variable (hK : ∀ k : K, k + k = 0)
include hK

/-- With the CCR oracle and the labels of the bits every wire carries, the reduction's entry is
the real half-gates ciphertext. -/
theorem entry_circularLabel_activeLabel (H : K × Bool → T → K × Bool) (tw : Slot C → T)
    (x : Fin n → Bool) (R : K) (W : Wire n C.size → K × Bool) (s : Slot C) :
    entry C H tw x (circularLabel H R) (activeLabel C W (offset R) x) s =
      garbleTable C H tw (offset R) W s := by
  have hc := add_add_cancel_label hK
  have hz := add_self_label hK
  have hb : ∀ c d : Bool, c + d + d = c := by decide
  obtain ⟨⟨g, h⟩, b⟩ := s
  simp only [entry, slotKnown, slotQuery, garbleTable, activeLabel]
  generalize C.program.trace interpretation x (left C g) = vl
  generalize C.program.trace interpretation x (right C g) = vr
  cases b <;>
    simp only [Bool.false_eq_true, ↓reduceIte, circularLabel_eq, genCt, evCt, snd_add_sel_offset,
      hb] <;>
    cases vl <;> cases vr <;> simp only [sel_false, sel_true, add_zero] <;>
    simp only [add_assoc, add_comm, add_left_comm, hc, hz, zero_add]

/-- With the CCR oracle for offset key `R`, the reduction's table on the labels `Z + x Δ` the
evaluator holds is the real garbled table for input zero labels `Z`. -/
theorem oracleTable_circularLabel (H : K × Bool → T → K × Bool) (tw : Slot C → T) (x : Fin n → Bool)
    (R : K) (Z : Fin n → K × Bool) :
    oracleTable C H tw x (circularLabel H R) (fun i => Z i + sel (x i) (offset R)) =
      garbleTable C H tw (offset R) (zeroLabels C H tw (offset R) Z) := by
  have hent : entry C H tw x (circularLabel H R)
      (activeLabel C (zeroLabels C H tw (offset R) Z) (offset R) x) =
      garbleTable C H tw (offset R) (zeroLabels C H tw (offset R) Z) :=
    funext (entry_circularLabel_activeLabel C hK H tw x R _)
  have hL : oracleLabels C H tw x (circularLabel H R) (fun i => Z i + sel (x i) (offset R)) =
      activeLabel C (zeroLabels C H tw (offset R) Z) (offset R) x :=
    (isLocal_entry C H tw x _ _).iterate_eq_of_isFixed 0 (by
      rw [hent]
      exact evalStep_activeLabel C hK H tw R Z x _ (zeroLabels_isFixed C H tw (offset R) Z))
  rw [oracleTable, hL, hent]

/-- The real view is the simulated view built from the evaluator's input labels and the
reduction's table with the CCR oracle. -/
theorem view_garbleWith (H : K × Bool → T → K × Bool) (tw : Slot C → T) (x : Fin n → Bool)
    (R : K) (Z : Fin n → K × Bool) :
    (garbleWith C H tw R Z).view x = simulateWith C H tw (C.eval interpretation x)
      (fun i => Z i + sel (x i) (offset R))
      (oracleTable C H tw x (circularLabel H R) (fun i => Z i + sel (x i) (offset R))) := by
  have hA := (isLocal_evalStep_const C H tw _ _).iterate_eq_of_isFixed 0
    (evalStep_activeLabel C hK H tw R Z x _ (zeroLabels_isFixed C H tw (offset R) Z))
  rw [oracleTable_circularLabel C hK]
  refine View.ext rfl rfl (funext fun o => ?_)
  simp only [Garbled.view, garbleWith, simulateWith, evaluate, evalLabels, hA, activeLabel,
    snd_add_sel_offset, Circuit.eval, Function.comp_apply]
  rw [add_assoc, BooleanRing.add_self, add_zero]

end Real

/-! ### Building the table with the oracle -/

section Table

variable (H : K × Bool → T → K × Bool) (tw : Slot C → T) (x : Fin n → Bool)

/-- The ciphertexts of gate `k`: query the oracle at the two slots of gate `k`, from the labels
the evaluator holds with the table `ct` built so far, and keep `ct` elsewhere. -/
noncomputable def gateStep (X : Fin n → K × Bool) (k : ℕ) (ct : Slot C → K × Bool) :
    ProbOracleComp (fun _ : (K × Bool) × T × Bool => K × Bool) (Slot C → K × Bool) := do
  let O ← ProbOracleComp.tabulate (slotQuery C tw x (evalLabels C H tw ct X))
    (Finset.univ.filter fun s : Slot C => (s.1.1 : ℕ) = k).toList
  return fun s => if (s.1.1 : ℕ) = k then slotKnown C H tw (evalLabels C H tw ct X) s + O s
    else ct s

/-- The table built from the gates below `k`. -/
noncomputable def tableRun (X : Fin n → K × Bool) :
    ℕ → ProbOracleComp (fun _ : (K × Bool) × T × Bool => K × Bool) (Slot C → K × Bool)
  | 0 => pure 0
  | k + 1 => do
    let ct ← tableRun X k
    gateStep C H tw x X k ct

/-- The table built from the gates below `k` against a fixed function. -/
def detRun (f : (K × Bool) × T × Bool → K × Bool) (X : Fin n → K × Bool) :
    ℕ → Slot C → K × Bool
  | 0 => 0
  | k + 1 => fun s => if (s.1.1 : ℕ) = k then entry C H tw x f (evalLabels C H tw
      (detRun f X k) X) s else detRun f X k s

theorem interpret_tableRun (f : (K × Bool) × T × Bool → K × Bool) (X : Fin n → K × Bool)
    (k : ℕ) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun q => pure (f q))
      (tableRun C H tw x X k) = pure (detRun C H tw x f X k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [tableRun, gateStep, OracleComp.interpret_bind, ih, pure_bind,
      ProbOracleComp.interpret_tabulate, OracleComp.interpret_pure]
    congr 1
    funext s
    by_cases h : (s.1.1 : ℕ) = k <;> simp [detRun, entry, h]

theorem detRun_eq (f : (K × Bool) × T × Bool → K × Bool) (X : Fin n → K × Bool) :
    detRun C H tw x f X C.size = oracleTable C H tw x f X := by
  have key : ∀ k (s : Slot C), (s.1.1 : ℕ) < k →
      detRun C H tw x f X k s = oracleTable C H tw x f X s := by
    intro k
    induction k with
    | zero => intro s hs; exact absurd hs (Nat.not_lt_zero _)
    | succ k ih =>
      intro s hs
      simp only [detRun]
      split_ifs with hk
      · rw [oracleTable, ← evalLabels_oracleTable]
        have hl := toNat_left_lt C s.1.1
        have hr := toNat_right_lt C s.1.1
        exact entry_congr C H tw x f s (evalLabels_congr C H tw X k ih _ (by omega))
          (evalLabels_congr C H tw X k ih _ (by omega))
      · exact ih s (by omega)
  exact funext fun s => key _ s s.1.1.isLt

end Table

/-! ### Experiments -/

variable [Fintype K] [Nonempty K]

/-- The simulator: uniform input labels and a uniform table. It sees the circuit and the output
`y`, but not the input. -/
noncomputable def simulate (H : K × Bool → T → K × Bool) (tw : Slot C → T) (y : Fin m → Bool) :
    ProbComp (View C K) := do
  let X ← ProbComp.uniform (Fin n → K × Bool)
  let ct ← ProbComp.uniform (Slot C → K × Bool)
  return simulateWith C H tw y X ct

/-- The real privacy experiment: garble `C`, and run `D` on the view of the garbled circuit on
`x`. -/
@[expose] noncomputable def realGame (H : K × Bool → T → K × Bool) (tw : Slot C → T)
    (x : Fin n → Bool) (D : View C K → ProbComp Bool) : Game :=
  ProbComp.eval do
    let G ← garble C H tw
    D (G.view x)

/-- The simulated privacy experiment: run `D` on a view simulated from `C` and its output on
`x`. -/
@[expose] noncomputable def simGame (H : K × Bool → T → K × Bool) (tw : Slot C → T)
    (x : Fin n → Bool) (D : View C K → ProbComp Bool) : Game :=
  ProbComp.eval do
    let V ← simulate C H tw (C.eval interpretation x)
    D V

/-! ### The reduction -/

section Reduction

variable (H : K × Bool → T → K × Bool) (tw : Slot C → T) (x : Fin n → Bool)

/-- The CCR adversary: sample the input labels the evaluator holds, build the table gate by gate
with the oracle, and run `D` on the resulting simulated view. -/
noncomputable def reduction (D : View C K → ProbComp Bool) :
    ProbOracleComp (fun _ : (K × Bool) × T × Bool => K × Bool) Bool := do
  let X ← ProbOracleComp.sample (ProbComp.uniform (Fin n → K × Bool))
  let ct ← tableRun C H tw x X C.size
  ProbOracleComp.sample (D (simulateWith C H tw (C.eval interpretation x) X ct))

theorem eval_interpret_reduction (D : View C K → ProbComp Bool)
    (f : (K × Bool) × T × Bool → K × Bool) :
    ProbComp.eval (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin
        fun q => pure (f q)) (reduction C H tw x D)) =
      (PMF.uniformOfFintype (Fin n → K × Bool)).bind fun X =>
        ProbComp.eval (D (simulateWith C H tw (C.eval interpretation x) X
          (oracleTable C H tw x f X))) := by
  have hself : ∀ {α : Type} (p : ProbComp α), OracleComp.interpret ProbComp.unifFin p = p :=
    fun p => OracleComp.interpret_query_eq_self p
  simp only [reduction, OracleComp.interpret_bind, ProbOracleComp.interpret_sample, hself,
    interpret_tableRun, detRun_eq, pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform]

/-- The real experiment is the CCR game with the reduction and the keyed oracle. -/
theorem realGame_reduction (hK : ∀ k : K, k + k = 0) (D : View C K → ProbComp Bool) :
    PRF.realGame (circularLabel H) (reduction C H tw x D) = realGame C H tw x D := by
  simp only [PRF.realGame, realGame, garble, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_interpret_reduction, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  have hshift : ∀ (c : Fin n → K × Bool) (g : (Fin n → K × Bool) → PMF Bool),
      (PMF.uniformOfFintype _).bind (fun Z => g (Z + c)) = (PMF.uniformOfFintype _).bind g := by
    intro c g
    conv_rhs => rw [← Probability.PMF.uniformOfFintype_map_equiv (Equiv.addRight c)]
    rw [PMF.bind_map]
    rfl
  congr 1
  funext R
  refine (hshift (fun i => sel (x i) (offset R)) _).symm.trans ?_
  congr 1
  funext Z
  exact congrArg (fun V => ProbComp.eval (D V)) (view_garbleWith C hK H tw x R Z).symm

variable [Fintype T] [DecidableEq T] [DecidableEq K]

/-- **Against a random function the reduction's table is uniform**, for each choice of input
labels, when distinct slots have distinct tweaks. -/
theorem map_oracleTable (htw : Function.Injective tw) (X : Fin n → K × Bool) :
    (PMF.uniformOfFintype ((K × Bool) × T × Bool → K × Bool)).map
      (fun f => oracleTable C H tw x f X) = PMF.uniformOfFintype (Slot C → K × Bool) := by
  ext ct
  have hu := congrArg (fun p => p fun s => ct s - slotKnown C H tw (evalLabels C H tw ct X) s)
    (Probability.PMF.uniformOfFintype_map_comp (R := K × Bool)
      (slotQuery_injective C tw x htw (evalLabels C H tw ct X)))
  simp only [PMF.map_apply] at hu ⊢
  rw [PMF.uniformOfFintype_apply] at hu ⊢
  rw [← hu]
  refine tsum_congr fun f => ?_
  congr 1
  exact propext ⟨fun h => ((oracleTable_eq_iff C H tw x f X ct).1 h.symm).symm,
    fun h => ((oracleTable_eq_iff C H tw x f X ct).2 h.symm).symm⟩

/-- The simulated experiment is the CCR game with the reduction and a random function. -/
theorem simGame_reduction (htw : Function.Injective tw) (D : View C K → ProbComp Bool) :
    PRF.idealGame (reduction C H tw x D) = simGame C H tw x D := by
  simp only [PRF.idealGame, simGame, simulate, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_interpret_reduction, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm]
  congr 1
  funext X
  rw [← map_oracleTable C H tw x htw X, PMF.bind_map]
  rfl

/-- **Simulation privacy of half-gates garbling.** For every circuit `C`, input `x` and
distinguisher `D`, if distinct slots have distinct tweaks and every element of `K` is its own
negative, the advantage of `D` between the real and the simulated view equals the circular
correlation robustness advantage `CorrelationRobust.advantageLabel H` of the reduction. The
identity tweak map, with `T = Slot C`, has distinct tweaks. -/
theorem advantage_realGame_simGame (hK : ∀ k : K, k + k = 0) (htw : Function.Injective tw)
    (D : View C K → ProbComp Bool) :
    Game.advantage (realGame C H tw x D) (simGame C H tw x D) =
      advantageLabel H (reduction C H tw x D) := by
  rw [advantageLabel, PRF.advantage, realGame_reduction C H tw x hK, simGame_reduction C H tw x htw]

end Reduction

end Cslib.Crypto.Garbling.HalfGates
