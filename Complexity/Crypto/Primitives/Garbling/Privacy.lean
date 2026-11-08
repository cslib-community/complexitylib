/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Crypto.Primitives.Garbling.Basic
public import Complexity.Crypto.Primitives.PRF.Finite
public import Complexity.Languages.Probabilistic.Oracle.Tabulate
import Complexity.Computability.Circuit.Program
import Complexity.Crypto.Game.Hybrid
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Product
import Complexity.Probability.Uniform

/-!
# Simulation-based privacy of garbled circuits

The evaluator of a garbled circuit sees a `View`: the garbled table, one label per input wire and
the output decoding information. Privacy in the simulation sense of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012] with topology side information asks for a simulator that produces an
indistinguishable view from the circuit's topology and its output alone. The simulator `simulate`
samples one uniform label per wire, writes in each gate's row named by its arguments' labels the
gate's label masked under their keys, fills every other row uniformly, and sets the decoding bits
so that the output labels decode to the output. It never sees the gate operations or the input.

The main theorem `advantage_realGame_simGame_le` bounds the advantage of every distinguisher `D`
between the real view and the simulated view, for a circuit `C` and an input `x`, by the sum over
the `n + C.size` wires of the PRF advantage of an explicit reduction `reduction C I F tw x D j`
against `F`, provided the tweaks of distinct argument slots are distinct. The proof is a hybrid
argument over the wires in wire-number order: hybrid `j` replaces by uniform values the rows that
read an inactive label on a wire numbered below `j`. The reduction for wire `j` embeds the PRF
key as the inactive key of wire `j`: with the keyed oracle it produces hybrid `j` exactly
(`PRF.realGame` side), and with a random function hybrid `j + 1` exactly (`PRF.idealGame` side).
Each reduction reads the oracle up front at the tweaks of all argument slots, with at most one
query per slot (`isQueryBounded_reduction`), and runs `D` once. When every reduction has PRF
advantage at most `ε` the advantage is at most `(n + C.size) * ε`
(`advantage_realGame_simGame_le_mul`).

Tweak injectivity is needed. Take a row that reads one wire twice with the same colour. If its
two argument slots had equal tweaks, their mask terms would be equal and cancel in the `Bool`
component, so for a binary gate that row's colour bit would be sent in the clear. The identity on
`Slot C.topology` is an injective tweak map.

The simulator is correct: on an ordered topology every simulated view decodes to the output
(`View.run_simulateWith`).

This is the single-instance form of simulation privacy: the circuit, input and distinguisher are
fixed, so a bound uniform over a class of distinguishers follows by bounding the PRF advantage of
the corresponding reductions. No bound holds for arbitrary distinguishers, since an exhaustive
key search distinguishes once `K` is fixed. In the prv.sim game of [BellareHoangRogaway2012] the
adversary itself chooses the circuit and the input, possibly at random and keeping state for its
guess; a bound for that game follows from this one by averaging over the adversary's choice, since
the advantage of a mixture is at most the average advantage. That transfer is not formalized here.
Running time is not tracked either: there are no cost bounds for garbling, evaluation, the
simulator or the reductions.

## Main definitions

* `Cslib.Crypto.Garbling.View`: what the evaluator sees.
* `Cslib.Crypto.Garbling.simulateWith`, `Cslib.Crypto.Garbling.simulate`: the simulator.
* `Cslib.Crypto.Garbling.realGame`, `Cslib.Crypto.Garbling.simGame`: the privacy experiments.
* `Cslib.Crypto.Garbling.reduction`: the PRF adversary for one hybrid step.

## Main results

* `Cslib.Crypto.Garbling.View.run_simulateWith`: simulated views decode to the output.
* `Cslib.Crypto.Garbling.isQueryBounded_reduction`: at most one query per slot.
* `Cslib.Crypto.Garbling.advantage_realGame_simGame_le`: privacy, as a sum of PRF advantages.
* `Cslib.Crypto.Garbling.advantage_realGame_simGame_le_mul`: privacy with a uniform PRF bound.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
* [Y. Lindell, B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009]
-/

public section

namespace Cslib.Crypto.Garbling

open Cslib.Circuits Probability

universe v

variable {σ : Signature.{v}} {n m s : ℕ} {K T : Type}

/-- What the evaluator of a garbled circuit sees: the garbled table, one label per input wire and
the output decoding information. The topology is public, as an index of the type. -/
@[ext] structure View (τ : Circuit.Topology n m s) (K : Type) where
  /-- The garbled table. -/
  table : Row τ → K × Bool
  /-- The label of each input wire. -/
  input : Fin n → K × Bool
  /-- The decoding bit of each output wire. -/
  decoding : Fin m → Bool

/-- The view of a garbled circuit on an input. -/
@[expose] def Garbled.view {τ : Circuit.Topology n m s} (G : Garbled τ K) (x : Fin n → Bool) :
    View τ K where
  table := G.table
  input := encode G.encoding x
  decoding := G.decoding

variable [AddCommGroup K]

/-- Evaluate a view and decode the result. -/
@[expose] def View.run {τ : Circuit.Topology n m s} (V : View τ K) (F : K → T → K × Bool)
    (tw : Slot τ → T) : Fin m → Bool :=
  decode V.decoding (evaluate τ F tw V.table V.input)

/-- Running the view of a garbled circuit on `x` is running the garbled circuit on `x`. -/
theorem Garbled.run_view {τ : Circuit.Topology n m s} (G : Garbled τ K) (F : K → T → K × Bool)
    (tw : Slot τ → T) (x : Fin n → Bool) : (G.view x).run F tw = G.run F tw x := rfl

/-- The simulated view for wire labels `A` and filler rows `R`: input wires carry their labels;
the row of each gate named by its arguments' colours holds the gate's label masked under their
keys; every other row is filler; the decoding bits make the output labels decode to `y`. -/
def simulateWith (τ : Circuit.Topology n m s) (F : K → T → K × Bool) (tw : Slot τ → T)
    (y : Fin m → Bool) (A : Wire n s → K × Bool) (R : Row τ → K × Bool) : View τ K where
  table r := if r.2 = fun k => (A (τ.wires r.1 k)).2 then
      A (.gate r.1) + ∑ k, F (A (τ.wires r.1 k)).1 (tw ⟨r, k⟩)
    else R r
  input i := A (.input i)
  decoding o := (A (τ.outputs o)).2 + y o

/-- **Simulator correctness**: on an ordered topology every simulated view decodes to `y`. -/
theorem View.run_simulateWith {τ : Circuit.Topology n m s} (hτ : τ.IsOrdered)
    (F : K → T → K × Bool) (tw : Slot τ → T) (y : Fin m → Bool) (A : Wire n s → K × Bool)
    (R : Row τ → K × Bool) : (simulateWith τ F tw y A R).run F tw = y := by
  have hA : ∀ w, evalStep τ F tw (simulateWith τ F tw y A R).table
      (simulateWith τ F tw y A R).input A w = A w := by
    intro w
    cases w with
    | input i => rfl
    | gate g =>
      simp only [evalStep, simulateWith, ite_true]
      exact add_sub_cancel_right _ _
  funext o
  rw [View.run, evaluate_eq_of_evalStep hτ F tw _ _ A hA]
  simp only [decode, Function.comp_apply, simulateWith]
  rw [← add_assoc, BooleanRing.add_self, zero_add]

/-! ### Hybrid views -/

/-- The active colour of each wire on input `x`. -/
private def act (C : Circuit σ n m) (I : Interpretation σ Bool) (x : Fin n → Bool)
    (perm : Wire n C.size → Bool) (w : Wire n C.size) : Bool :=
  C.program.trace I x w + perm w

/-- A row reads an inactive colour on some wire numbered below `j`. -/
private def Hidden {τ : Circuit.Topology n m s} (a : Wire n s → Bool) (j : ℕ) (r : Row τ) : Prop :=
  ∃ k, r.2 k ≠ a (τ.wires r.1 k) ∧ (τ.wires r.1 k).toNat < j

private instance {τ : Circuit.Topology n m s} (a : Wire n s → Bool) (j : ℕ) (r : Row τ) :
    Decidable (Hidden a j r) := by
  unfold Hidden; infer_instance

/-- A slot reads the inactive colour of wire `j`. -/
private def IsTarget {τ : Circuit.Topology n m s} (a : Wire n s → Bool) (j : ℕ) (p : Slot τ) :
    Prop :=
  p.1.2 p.2 ≠ a (τ.wires p.1.1 p.2) ∧ (τ.wires p.1.1 p.2).toNat = j

private instance {τ : Circuit.Topology n m s} (a : Wire n s → Bool) (j : ℕ) (p : Slot τ) :
    Decidable (IsTarget a j p) := by
  unfold IsTarget; infer_instance

/-- Hybrid view `j` with oracle `O`: rows reading an inactive colour below wire `j` are taken
from `R`; in the other rows, the mask term of each slot reading the inactive colour of wire `j`
is the oracle's answer. -/
private def hybridView (C : Circuit σ n m) (I : Interpretation σ Bool) (F : K → T → K × Bool)
    (tw : Slot C.topology → T) (x : Fin n → Bool) (j : ℕ) (key : Wire n C.size × Bool → K)
    (perm : Wire n C.size → Bool) (R : Row C.topology → K × Bool)
    (O : Slot C.topology → K × Bool) : View C.topology K where
  table r := if Hidden (act C I x perm) j r then R r else
    plainRow C I key perm r + ∑ k, if IsTarget (act C I x perm) j ⟨r, k⟩ then O ⟨r, k⟩ else
      F (key (C.topology.wires r.1 k, r.2 k)) (tw ⟨r, k⟩)
  input := encode (inputEncoding key perm) x
  decoding := outputDecoding C perm

/-- The keyed function at the slot's own key and tweak. -/
private def realOracle (C : Circuit σ n m) (F : K → T → K × Bool) (tw : Slot C.topology → T)
    (key : Wire n C.size × Bool → K) (p : Slot C.topology) : K × Bool :=
  F (key (C.topology.wires p.1.1 p.2, p.1.2 p.2)) (tw p)

private theorem hybridView_realOracle_table (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool) (j : ℕ)
    (key : Wire n C.size × Bool → K) (perm : Wire n C.size → Bool)
    (R : Row C.topology → K × Bool) (r : Row C.topology) :
    (hybridView C I F tw x j key perm R (realOracle C F tw key)).table r =
      if Hidden (act C I x perm) j r then R r else garbleTable C I F tw key perm r := by
  simp only [hybridView, realOracle, ite_self, garbleTable, rowMask]

/-- With the keyed oracle at key `k`, the reduction's view is hybrid view `j` with `k` as the
inactive key of wire `j`. -/
private theorem hybridView_update (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool) (j : ℕ)
    (w : Wire n C.size) (hw : w.toNat = j) (k : K) (key : Wire n C.size × Bool → K)
    (perm : Wire n C.size → Bool) (R : Row C.topology → K × Bool) :
    hybridView C I F tw x j key perm R (fun p => F k (tw p)) =
      hybridView C I F tw x j (Function.update key (w, !act C I x perm w) k) perm R
        (realOracle C F tw (Function.update key (w, !act C I x perm w) k)) := by
  ext1
  · funext r
    simp only [hybridView]
    split_ifs with h
    · rfl
    · congr 1
      · simp only [plainRow]
        rw [Function.update_of_ne]
        intro heq
        have hg : Wire.gate r.1 = w := congrArg Prod.fst heq
        have hc := congrArg Prod.snd heq
        dsimp only at hc
        apply Bool.ne_not.mpr (rfl : act C I x perm w = act C I x perm w)
        rw [← hc, ← hg]
        have hρ : ∀ k, r.2 k = act C I x perm (C.topology.wires r.1 k) := by
          intro k
          by_contra hk
          exact h ⟨k, hk, hw ▸ hg ▸ C.isOrdered_topology r.1 k⟩
        simp only [act]
        congr 1
        rw [C.program.trace_gate]
        congr 1 with k : 1
        rw [hρ k]
        have hcancel : ∀ a b : Bool, a = a + b + b := fun a b => by
          rw [add_assoc, BooleanRing.add_self, add_zero]
        exact hcancel _ _
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [realOracle]
        split_ifs with ht
        · obtain ⟨hne, hidx⟩ := ht
          have hwi : C.topology.wires r.1 i = w := Wire.toNat_injective (hidx.trans hw.symm)
          rw [hwi] at hne
          rw [hwi, Bool.eq_not_of_ne hne, Function.update_self]
        · rw [Function.update_of_ne]
          intro heq
          apply ht
          have hwi : C.topology.wires r.1 i = w := congrArg Prod.fst heq
          have hc : r.2 i = !act C I x perm w := congrArg Prod.snd heq
          refine ⟨?_, hwi ▸ hw⟩
          rw [hc, hwi]
          exact (Bool.ne_not.mpr rfl).symm
  · funext i
    simp only [hybridView, encode, inputEncoding]
    rw [Function.update_of_ne]
    intro heq
    have hg : Wire.input i = w := congrArg Prod.fst heq
    have hc := congrArg Prod.snd heq
    dsimp only at hc
    apply Bool.ne_not.mpr (rfl : act C I x perm w = act C I x perm w)
    rw [← hc, ← hg]
    rfl
  · rfl

/-- Masking the colour of each wire by an independent bit and keeping the key of the active
colour separately is a bijection. -/
private def maskEquiv {W : Type} (v : W → Bool) :
    (W × Bool → K) × (W → Bool) ≃ (W → K × Bool) × (W → K) where
  toFun p := (fun w => (p.1 (w, v w + p.2 w), v w + p.2 w), fun w => p.1 (w, !(v w + p.2 w)))
  invFun q := (fun wc => if wc.2 = (q.1 wc.1).2 then (q.1 wc.1).1 else q.2 wc.1,
    fun w => (q.1 w).2 + v w)
  left_inv p := by
    obtain ⟨key, perm⟩ := p
    have hperm : ∀ w, v w + perm w + v w = perm w := fun w => by
      rw [add_comm, ← add_assoc, BooleanRing.add_self, zero_add]
    refine Prod.ext (funext fun ⟨w, c⟩ => ?_) (funext hperm)
    dsimp only
    split_ifs with h
    · rw [h]
    · rw [Bool.eq_not_of_ne h]
  right_inv q := by
    obtain ⟨A, B⟩ := q
    have hcol : ∀ w, v w + ((A w).2 + v w) = (A w).2 := fun w => by
      rw [add_comm, add_assoc, BooleanRing.add_self, add_zero]
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · dsimp only
      rw [hcol, ite_eq_left rfl]
    · dsimp only
      rw [hcol, ite_eq_right (Bool.ne_not.mpr rfl).symm]

/-- A map from a uniform input whose values are fixed off a set `U` of coordinates, and whose
translations on `U` are realized by permutations of the input, is uniform on `U`. -/
private theorem uniformOfFintype_map_eq_of_shift {Ω ι L : Type} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι] [AddCommGroup L] [Fintype L]
    (U : ι → Prop) [DecidablePred U] (z : ι → L) (f : Ω → ι → L)
    (hout : ∀ ω i, ¬ U i → f ω i = z i)
    (hshift : ∀ c : ι → L, ∃ e : Equiv.Perm Ω, ∀ ω i, U i → f (e ω) i = f ω i + c i) :
    (PMF.uniformOfFintype Ω).map f =
      (PMF.uniformOfFintype ({i // U i} → L)).map fun u i => if h : U i then u ⟨i, h⟩ else z i := by
  let extend : ({i // U i} → L) → ι → L := fun u i => if h : U i then u ⟨i, h⟩ else z i
  have hf : f = extend ∘ fun ω (i : {i // U i}) => f ω i := by
    funext ω i
    by_cases h : U i
    · simp [extend, h]
    · simp [extend, h, hout ω i h]
  rw [hf, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_of_shift]
  intro c
  obtain ⟨e, he⟩ := hshift (fun i => if h : U i then c ⟨i, h⟩ else 0)
  exact ⟨e, fun ω => funext fun i => by simp [he _ _ i.2, i.2]⟩

/-- Against a random oracle, hybrid view `j` can absorb any shift `c` of the rows hidden in hybrid
`j + 1` by a translation of (oracle, filler rows). Rows already hidden in hybrid `j` are filler, so
the filler absorbs their shift. Every other such row reads the inactive colour of wire `j` in at least
one slot; the oracle is shifted at the tweak of the first such slot of each row. Distinct slots have
distinct tweaks, so this shifts exactly one mask term of the row. -/
private theorem exists_perm_hybridView_table_add (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (htw : Function.Injective tw)
    (x : Fin n → Bool) (j : ℕ) (key : Wire n C.size × Bool → K) (perm : Wire n C.size → Bool)
    (c : Row C.topology → K × Bool) :
    ∃ e : Equiv.Perm ((T → K × Bool) × (Row C.topology → K × Bool)), ∀ ω r,
      Hidden (act C I x perm) (j + 1) r →
        (hybridView C I F tw x j key perm (e ω).2 fun p => (e ω).1 (tw p)).table r =
          (hybridView C I F tw x j key perm ω.2 fun p => ω.1 (tw p)).table r + c r := by
  classical
  -- The first slot of its row that reads the inactive colour of wire `j`.
  let First : Slot C.topology → Prop := fun p =>
    IsTarget (act C I x perm) j p ∧ ∀ k, IsTarget (act C I x perm) j ⟨p.1, k⟩ → p.2 ≤ k
  let δ : T → K × Bool := Function.extend tw (fun p => if First p then c p.1 else 0) 0
  have hδ (p : Slot C.topology) : δ (tw p) = if First p then c p.1 else 0 :=
    htw.extend_apply _ _ p
  refine ⟨Equiv.addRight (δ, c), fun ω r hr => ?_⟩
  simp only [hybridView, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  by_cases h : Hidden (act C I x perm) j r
  · rw [ite_eq_left h, ite_eq_left h]
  rw [ite_eq_right h, ite_eq_right h]
  -- Some slot of `r` reads the inactive colour of wire `j`; let `k₀` be the first one.
  obtain ⟨k₁, hk₁, hlt₁⟩ := hr
  have htk₁ : IsTarget (act C I x perm) j ⟨r, k₁⟩ := by
    refine ⟨hk₁, ?_⟩
    change (C.topology.wires r.1 k₁).toNat = j
    by_contra hne
    exact h ⟨k₁, hk₁, by omega⟩
  let S := Finset.univ.filter fun k => IsTarget (act C I x perm) j ⟨r, k⟩
  have hS : S.Nonempty := ⟨k₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htk₁⟩⟩
  have hFirst (k : Fin _) : First ⟨r, k⟩ ↔ k = S.min' hS := by
    constructor
    · intro hk
      exact le_antisymm (hk.2 _ (Finset.mem_filter.mp (S.min'_mem hS)).2)
        (S.min'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.1⟩))
    · rintro rfl
      exact ⟨(Finset.mem_filter.mp (S.min'_mem hS)).2,
        fun k hk => S.min'_le k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)⟩
  -- The oracle shifts summed over the target slots of `r` give exactly `c r`.
  have hδsum : (∑ k, if IsTarget (act C I x perm) j ⟨r, k⟩ then δ (tw ⟨r, k⟩) else 0) = c r := by
    have hterm (k : Fin _) : (if IsTarget (act C I x perm) j ⟨r, k⟩ then δ (tw ⟨r, k⟩) else 0) =
        if k = S.min' hS then c r else 0 := by
      rw [hδ]
      by_cases hk : k = S.min' hS
      · have hk' := (hFirst k).mpr hk
        rw [ite_eq_left hk, ite_eq_left hk', ite_eq_left hk'.1]
      · have hk' := mt (hFirst k).mp hk
        rw [ite_eq_right hk, ite_eq_right hk', ite_self]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Fintype.sum_ite_eq']
  rw [add_assoc, ← hδsum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rfl
  · exact (add_zero _).symm

variable [Fintype K] [Nonempty K]

/-! ### Experiments -/

/-- The simulator: uniform wire labels and uniform filler rows. It sees only the topology, the
public keyed function and tweaks, and the output. -/
noncomputable def simulate (τ : Circuit.Topology n m s) (F : K → T → K × Bool) (tw : Slot τ → T)
    (y : Fin m → Bool) : ProbComp (View τ K) := do
  let A ← ProbComp.uniform (Wire n s → K × Bool)
  let R ← ProbComp.uniform (Row τ → K × Bool)
  return simulateWith τ F tw y A R

/-- The real privacy experiment: garble `C`, and run `D` on the view of the garbled circuit on
`x`. -/
@[expose] noncomputable def realGame (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) : Game :=
  ProbComp.eval do
    let G ← garble C I F tw
    D (G.view x)

/-- The simulated privacy experiment: run `D` on a view simulated from the topology of `C` and
its output on `x`. -/
@[expose] noncomputable def simGame (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) : Game :=
  ProbComp.eval do
    let V ← simulate C.topology F tw (C.eval I x)
    D V

/-! ### The hybrid argument -/

/-- Hybrid experiment `j`. -/
private noncomputable def hybridGame (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) (j : ℕ) : Game :=
  ProbComp.eval do
    let key ← ProbComp.uniform (Wire n C.size × Bool → K)
    let perm ← ProbComp.uniform (Wire n C.size → Bool)
    let R ← ProbComp.uniform (Row C.topology → K × Bool)
    D (hybridView C I F tw x j key perm R (realOracle C F tw key))

/-- The PRF adversary for hybrid step `j`: sample keys, permutation bits and filler rows, query
the oracle at the tweak of every argument slot, build hybrid view `j` with the answers in place
of the mask terms on the inactive colour of wire `j`, and run `D` on it. -/
noncomputable def reduction (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) (j : ℕ) :
    ProbOracleComp (fun _ : T => K × Bool) Bool := do
  let key ← ProbOracleComp.sample (ProbComp.uniform (Wire n C.size × Bool → K))
  let perm ← ProbOracleComp.sample (ProbComp.uniform (Wire n C.size → Bool))
  let R ← ProbOracleComp.sample (ProbComp.uniform (Row C.topology → K × Bool))
  let O ← ProbOracleComp.tabulate tw (Finset.univ : Finset (Slot C.topology)).toList
  ProbOracleComp.sample (D (hybridView C I F tw x j key perm R O))

/-- Each reduction makes at most one oracle query per argument slot of the garbled table. -/
theorem isQueryBounded_reduction (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) (j : ℕ) :
    (reduction C I F tw x D j).IsQueryBounded (Fintype.card (Slot C.topology)) := by
  have h := (ProbOracleComp.IsQueryBounded.sample (spec := fun _ : T => K × Bool)
    (ProbComp.uniform (Wire n C.size × Bool → K))).bind fun key =>
    (ProbOracleComp.IsQueryBounded.sample (ProbComp.uniform (Wire n C.size → Bool))).bind
      fun perm =>
    (ProbOracleComp.IsQueryBounded.sample (ProbComp.uniform (Row C.topology → K × Bool))).bind
      fun R =>
    (ProbOracleComp.isQueryBounded_tabulate (R := K × Bool) tw
      (Finset.univ : Finset (Slot C.topology)).toList).bind fun O =>
    ProbOracleComp.IsQueryBounded.sample (D (hybridView C I F tw x j key perm R O))
  rw [Finset.length_toList, Finset.card_univ] at h
  simp only [Nat.zero_add, Nat.add_zero] at h
  exact h

/-- Against the keyed oracle the reduction samples hybrid view `j` with the oracle in place of
the mask terms. -/
private theorem eval_interpret_reduction (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) (j : ℕ) (f : T → K × Bool) :
    ProbComp.eval (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin
        fun t => pure (f t)) (reduction C I F tw x D j)) =
      (PMF.uniformOfFintype (Wire n C.size × Bool → K)).bind fun key =>
        (PMF.uniformOfFintype (Wire n C.size → Bool)).bind fun perm =>
          (PMF.uniformOfFintype (Row C.topology → K × Bool)).bind fun R =>
            ProbComp.eval (D (hybridView C I F tw x j key perm R fun p => f (tw p))) := by
  have hself : ∀ {α : Type} (p : ProbComp α), OracleComp.interpret ProbComp.unifFin p = p :=
    fun p => OracleComp.interpret_query_eq_self p
  simp only [reduction, OracleComp.interpret_bind, ProbOracleComp.interpret_sample, hself,
    ProbOracleComp.interpret_tabulate, pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform,
    Finset.mem_toList, Finset.mem_univ, ite_true]

/-- Hybrid `0` is the real experiment. -/
private theorem hybridGame_zero (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) :
    hybridGame C I F tw x D 0 = realGame C I F tw x D := by
  have hv : ∀ key perm R, hybridView C I F tw x 0 key perm R (realOracle C F tw key) =
      (garbleWith C I F tw key perm).view x := by
    intro key perm R
    ext1
    · funext r
      rw [hybridView_realOracle_table, ite_eq_right]
      · rfl
      · rintro ⟨k, -, hk⟩
        exact Nat.not_lt_zero _ hk
    · rfl
    · rfl
  simp only [hybridGame, realGame, garble, hv, bind_assoc, pure_bind, ProbComp.eval_bind,
    ProbComp.eval_uniform, PMF.bind_const]

/-- The last hybrid is the simulated experiment. -/
private theorem hybridGame_last (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) :
    hybridGame C I F tw x D (n + C.size) = simGame C I F tw x D := by
  have hv : ∀ key perm R, hybridView C I F tw x (n + C.size) key perm R (realOracle C F tw key) =
      simulateWith C.topology F tw (C.eval I x)
        (fun w => (key (w, act C I x perm w), act C I x perm w)) R := by
    intro key perm R
    ext1
    · funext r
      rw [hybridView_realOracle_table]
      obtain ⟨g, ρ⟩ := r
      simp only [simulateWith]
      by_cases h : ρ = fun k => act C I x perm (C.topology.wires g k)
      · subst h
        rw [ite_eq_right, ite_eq_left rfl]
        · simp only [garbleTable, rowMask]
          exact congrArg (· + _) (plainRow_trace C I key perm x g)
        · rintro ⟨k, hk, -⟩
          exact hk rfl
      · rw [ite_eq_right h, ite_eq_left]
        obtain ⟨k, hk⟩ := Function.ne_iff.mp h
        exact ⟨k, hk, Wire.toNat_lt _⟩
    · rfl
    · funext o
      change perm (C.outputs o) = C.program.trace I x (C.outputs o) + perm (C.outputs o) +
        C.program.trace I x (C.outputs o)
      rw [add_comm, ← add_assoc, BooleanRing.add_self, zero_add]
  simp only [hybridGame, simGame, simulate, hv, bind_assoc, pure_bind, ProbComp.eval_bind,
    ProbComp.eval_uniform]
  exact Cslib.Probability.PMF.uniformOfFintype_bind_bind_fst_equiv
    (maskEquiv (K := K) (C.program.trace I x)) (fun A =>
      (PMF.uniformOfFintype (Row C.topology → K × Bool)).bind fun R =>
        ProbComp.eval (D (simulateWith C.topology F tw (C.eval I x) A R)))

/-- Against the keyed oracle, reduction `j` plays hybrid `j`. -/
private theorem realGame_reduction (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (x : Fin n → Bool)
    (D : View C.topology K → ProbComp Bool) (j : ℕ) (hj : j < n + C.size) :
    PRF.realGame F (reduction C I F tw x D j) = hybridGame C I F tw x D j := by
  let w : Wire n C.size := Wire.ofNat j hj
  have hw : w.toNat = j := Wire.toNat_ofNat j hj
  simp only [PRF.realGame, hybridGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_interpret_reduction, hybridView_update C I F tw x j w hw]
  simp only [PMF.bind_comm (PMF.uniformOfFintype (Wire n C.size × Bool → K))
      (PMF.uniformOfFintype (Wire n C.size → Bool)),
    PMF.bind_comm (PMF.uniformOfFintype K) (PMF.uniformOfFintype (Wire n C.size → Bool))]
  congr 1 with perm : 1
  conv_rhs => rw [← Cslib.Probability.PMF.uniformOfFintype_update (w, !act C I x perm w) (γ := K)]
  simp only [PMF.bind_bind, PMF.bind_map]
  rfl

variable [Fintype T] [DecidableEq T]

/-- Against a random function, reduction `j` plays hybrid `j + 1`, when distinct slots have
distinct tweaks. -/
private theorem idealGame_reduction (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (htw : Function.Injective tw)
    (x : Fin n → Bool) (D : View C.topology K → ProbComp Bool) (j : ℕ) :
    PRF.idealGame (reduction C I F tw x D j) = hybridGame C I F tw x D (j + 1) := by
  classical
  simp only [PRF.idealGame, hybridGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_interpret_reduction]
  simp only [PMF.bind_comm (PMF.uniformOfFintype (T → K × Bool))
      (PMF.uniformOfFintype (Wire n C.size × Bool → K)),
    PMF.bind_comm (PMF.uniformOfFintype (T → K × Bool))
      (PMF.uniformOfFintype (Wire n C.size → Bool))]
  congr 1 with key : 1
  congr 1 with perm : 1
  let Ω := (T → K × Bool) × (Row C.topology → K × Bool)
  let G : (Row C.topology → K × Bool) → PMF Bool := fun tab =>
    ProbComp.eval (D ⟨tab, encode (inputEncoding key perm) x, outputDecoding C perm⟩)
  let Tl : Ω → Row C.topology → K × Bool := fun ω =>
    (hybridView C I F tw x j key perm ω.2 fun p => ω.1 (tw p)).table
  let Tr : Ω → Row C.topology → K × Bool := fun ω =>
    (hybridView C I F tw x (j + 1) key perm ω.2 (realOracle C F tw key)).table
  let a := act C I x perm
  have hL : ((PMF.uniformOfFintype (T → K × Bool)).bind fun f =>
      (PMF.uniformOfFintype (Row C.topology → K × Bool)).bind fun R =>
        ProbComp.eval (D (hybridView C I F tw x j key perm R fun p => f (tw p)))) =
      ((PMF.uniformOfFintype Ω).map Tl).bind G := by
    rw [PMF.bind_map, ← Cslib.Probability.PMF.uniformOfFintype_prod]
    simp only [PMF.bind_bind, PMF.bind_map]
    rfl
  have hR : ((PMF.uniformOfFintype (Row C.topology → K × Bool)).bind fun R =>
        ProbComp.eval (D (hybridView C I F tw x (j + 1) key perm R (realOracle C F tw key)))) =
      ((PMF.uniformOfFintype Ω).map Tr).bind G := by
    rw [PMF.bind_map, ← Cslib.Probability.PMF.uniformOfFintype_prod]
    simp only [PMF.bind_bind, PMF.bind_map]
    exact (PMF.bind_const _ _).symm
  rw [hL, hR]
  congr 1
  have hmono : ∀ r : Row C.topology, Hidden a j r → Hidden a (j + 1) r := by
    rintro r ⟨k, hk, hlt⟩
    exact ⟨k, hk, Nat.lt_succ_of_lt hlt⟩
  have htarget : ∀ r : Row C.topology, ∀ k, IsTarget a j ⟨r, k⟩ → Hidden a (j + 1) r := by
    rintro r k ⟨hk, heq⟩
    exact ⟨k, hk, heq ▸ Nat.lt_succ_self _⟩
  let z : Row C.topology → K × Bool := garbleTable C I F tw key perm
  have houtL : ∀ ω r, ¬ Hidden a (j + 1) r → Tl ω r = z r := by
    intro ω r hr
    simp only [Tl, hybridView, z, garbleTable, rowMask]
    rw [ite_eq_right (fun h => hr (hmono r h))]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ite_eq_right (fun h => hr (htarget r k h))]
  have houtR : ∀ ω r, ¬ Hidden a (j + 1) r → Tr ω r = z r := by
    intro ω r hr
    simp only [Tr, hybridView, z, garbleTable, rowMask, realOracle, ite_self]
    rw [ite_eq_right hr]
  have hshiftR : ∀ c : Row C.topology → K × Bool, ∃ e : Equiv.Perm Ω,
      ∀ ω r, Hidden a (j + 1) r → Tr (e ω) r = Tr ω r + c r := by
    intro c
    refine ⟨Equiv.addRight (0, c), fun ω r hr => ?_⟩
    simp only [Tr, hybridView, Equiv.coe_addRight]
    rw [ite_eq_left hr, ite_eq_left hr]
    rfl
  have hshiftL : ∀ c : Row C.topology → K × Bool, ∃ e : Equiv.Perm Ω,
      ∀ ω r, Hidden a (j + 1) r → Tl (e ω) r = Tl ω r + c r :=
    exists_perm_hybridView_table_add C I F tw htw x j key perm
  rw [uniformOfFintype_map_eq_of_shift (Hidden a (j + 1)) z Tl houtL hshiftL,
    uniformOfFintype_map_eq_of_shift (Hidden a (j + 1)) z Tr houtR hshiftR]

/-- **Simulation privacy of garbled circuits.** For every circuit `C`, input `x` and
distinguisher `D`, if distinct argument slots have distinct tweaks, the advantage of `D` between
the real and the simulated view is at most the sum, over the `n + C.size` wires, of the PRF
advantage of the reduction for that wire against `F`. The hypothesis `htw` cannot be dropped:
in a row reading one wire twice with the same colour, equal tweaks on the two slots make their
mask terms cancel in the `Bool` component. The identity tweak map, with `T = Slot C.topology`,
satisfies it. -/
theorem advantage_realGame_simGame_le (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (htw : Function.Injective tw)
    (x : Fin n → Bool) (D : View C.topology K → ProbComp Bool) :
    Game.advantage (realGame C I F tw x D) (simGame C I F tw x D) ≤
      ∑ j ∈ Finset.range (n + C.size), PRF.advantage F (reduction C I F tw x D j) := by
  rw [← hybridGame_zero, ← hybridGame_last]
  refine (Game.advantage_hybrid_le_sum _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [PRF.advantage, realGame_reduction C I F tw x D j (Finset.mem_range.mp hj),
    idealGame_reduction C I F tw htw x D j]

/-- **Simulation privacy with a uniform PRF bound.** If each reduction has PRF advantage at most
`ε`, the advantage between the real and the simulated view is at most `(n + C.size) * ε`. -/
theorem advantage_realGame_simGame_le_mul (C : Circuit σ n m) (I : Interpretation σ Bool)
    (F : K → T → K × Bool) (tw : Slot C.topology → T) (htw : Function.Injective tw)
    (x : Fin n → Bool) (D : View C.topology K → ProbComp Bool) (ε : NNReal)
    (hε : ∀ j < n + C.size, PRF.advantage F (reduction C I F tw x D j) ≤ ε) :
    Game.advantage (realGame C I F tw x D) (simGame C I F tw x D) ≤ (n + C.size) * ε := by
  refine (advantage_realGame_simGame_le C I F tw htw x D).trans ?_
  calc ∑ j ∈ Finset.range (n + C.size), PRF.advantage F (reduction C I F tw x D j)
      ≤ ∑ _j ∈ Finset.range (n + C.size), ε :=
        Finset.sum_le_sum fun j hj => hε j (Finset.mem_range.mp hj)
    _ = (n + C.size) * ε := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add]

end Cslib.Crypto.Garbling
