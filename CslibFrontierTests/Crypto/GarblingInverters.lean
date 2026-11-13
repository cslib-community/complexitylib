/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Primitives.Garbling.Adaptive
import CslibFrontier.Crypto.Primitives.Garbling.CircuitInverters

/-!
# Tests for conventional-circuit side-information inverters and `Prv1` adaptive privacy

Concrete conventional circuits separate `phiSize`, `phiTopo` and `phiCirc`; executable `decide`
checks verify that `mTopo` and `mSize` preserve topology and shape and evaluate to target outputs
on `0^n`; a concrete circuit scheme instantiates Proposition 1 and Corollaries 1 and 2 of
[BellareHoangRogaway2012]; and the `prv.sim`-to-`prv1` reduction of [BellareHoangRogaway2012b] is
instantiated.
-/

namespace CslibFrontierTests.Crypto.GarblingInverters

open Cslib Cslib.Crypto Cslib.Crypto.Garbling

/-- A 3-input, 1-output, 2-gate circuit: gate 0 (`wire 4`) computes `x₁ ∧ x₂`, and gate 1
(`wire 5`, the output wire) computes `x₂ ⊕ wire 4`. -/
def sampleCircuit : ConventionalCircuit where
  n := 3
  m := 1
  q := 2
  A := ![1, 2]
  B := ![2, 4]
  G i := if i.val = 0 then (· && ·) else xor

/-- A second 3-input, 1-output, 2-gate circuit with the same shape `(3, 1, 2)` as `sampleCircuit`
but different wiring: gate 0 reads wires `(1, 3)` instead of `(1, 2)`. -/
def sampleCircuit' : ConventionalCircuit where
  n := 3
  m := 1
  q := 2
  A := ![1, 2]
  B := ![3, 4]
  G i := if i.val = 0 then (· && ·) else xor

/-- A third circuit sharing the topology of `sampleCircuit` but replacing gate 0 with `||`. -/
def sampleCircuitSameTopo : ConventionalCircuit where
  n := 3
  m := 1
  q := 2
  A := ![1, 2]
  B := ![2, 4]
  G i := if i.val = 0 then (· || ·) else xor

theorem sampleCircuit_isValid : sampleCircuit.IsValid := by decide
theorem sampleCircuit'_isValid : sampleCircuit'.IsValid := by decide
theorem sampleCircuitSameTopo_isValid : sampleCircuitSameTopo.IsValid := by decide

/-- Bundled valid circuits for side-information and inverter checks. -/
def sampleValidCircuit : ValidCircuit := ⟨sampleCircuit, sampleCircuit_isValid⟩

/-- Second bundled valid circuit with the same shape `(3, 1, 2)` but different wiring. -/
def sampleValidCircuit' : ValidCircuit := ⟨sampleCircuit', sampleCircuit'_isValid⟩

/-- Third bundled valid circuit with the same topology as `sampleValidCircuit`. -/
def sampleValidCircuitSameTopo : ValidCircuit :=
  ⟨sampleCircuitSameTopo, sampleCircuitSameTopo_isValid⟩

example : sampleCircuit.evalCirc [true, true, false] = [false] := by decide
example : sampleCircuit.evalCirc [false, true, false] = [true] := by decide

example : phiSize.phi sampleValidCircuit = phiSize.phi sampleValidCircuit' ∧
    phiTopo.phi sampleValidCircuit ≠ phiTopo.phi sampleValidCircuit' := by
  decide

example : phiTopo.phi sampleValidCircuit = phiTopo.phi sampleValidCircuitSameTopo ∧
    phiCirc.phi sampleValidCircuit ≠ phiCirc.phi sampleValidCircuitSameTopo := by
  decide

example :
    let t := phiTopo.phi sampleValidCircuit
    let q := mTopo t [true]
    phiTopo.phi q.fn = t ∧ q.input = [false, false, false] ∧ q.fn.1.evalCirc q.input = [true] := by
  decide

example :
    let s := phiSize.phi sampleValidCircuit
    let q := mSize s [true]
    phiSize.phi q.fn = s ∧ q.input = [false, false, false] ∧ q.fn.1.evalCirc q.input = [true] := by
  decide

/-- A concrete circuit scheme over `ValidCircuit` with semantics `evalCirc`. -/
def plainCircuitScheme : Scheme ValidCircuit where
  inLen f := f.1.n
  outLen f := f.1.m
  size f := f.1.q
  ev f x := f.1.evalCirc x
  coinLen _ _ _ _ := 0
  gb _ f _ := ⟨[], [], List.replicate f.1.m false⟩
  encode _ x := x
  evalGarbled _ x := x
  decode d y := if y.length = d.length then some y else none

theorem plainCircuitScheme_isCircuitScheme : plainCircuitScheme.IsCircuitScheme :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩

example :
    prvIndValid plainCircuitScheme phiSize
      ⟨⟨sampleValidCircuit, [false, true, false]⟩,
        ⟨sampleValidCircuit', [false, true, false]⟩⟩ := by
  decide

example :
    ¬ prvIndValid plainCircuitScheme phiTopo
      ⟨⟨sampleValidCircuit, [false, true, false]⟩,
        ⟨sampleValidCircuit', [false, true, false]⟩⟩ := by
  decide

example {σ : Type} (k : ℕ) (B : PrvSimAdversary ValidCircuit σ) :
    prvSimAdvantage plainCircuitScheme phiTopo k (prvSimFromInverter plainCircuitScheme k mTopo) B =
      prvIndAdvantage plainCircuitScheme phiTopo k
        (prvSimToInd plainCircuitScheme phiTopo mTopo B) :=
  prvSimAdvantage_phiTopo_mTopo_eq plainCircuitScheme_isCircuitScheme k B

example {σ : Type} (k : ℕ) (B : PrvSimAdversary ValidCircuit σ) :
    prvSimAdvantage plainCircuitScheme phiSize k (prvSimFromInverter plainCircuitScheme k mSize) B =
      prvIndAdvantage plainCircuitScheme phiSize k
        (prvSimToInd plainCircuitScheme phiSize mSize B) :=
  prvSimAdvantage_phiSize_mSize_eq plainCircuitScheme_isCircuitScheme k B

example {σ : Type} (k : ℕ) (B : ObvSimAdversary ValidCircuit σ) :
    obvSimAdvantage plainCircuitScheme phiTopo k
        (obvSimFromInverter plainCircuitScheme k mTopoInv) B =
      obvIndAdvantage plainCircuitScheme phiTopo k
        (obvSimToInd plainCircuitScheme phiTopo mTopoInv B) :=
  obvSimAdvantage_phiTopo_mTopoInv_eq plainCircuitScheme_isCircuitScheme k B

example {σ : Type} (k : ℕ) (B : ObvSimAdversary ValidCircuit σ) :
    obvSimAdvantage plainCircuitScheme phiSize k
        (obvSimFromInverter plainCircuitScheme k mSizeInv) B =
      obvIndAdvantage plainCircuitScheme phiSize k
        (obvSimToInd plainCircuitScheme phiSize mSizeInv B) :=
  obvSimAdvantage_phiSize_mSizeInv_eq plainCircuitScheme_isCircuitScheme k B

/-- A stateful `Prv1Simulator` for `plainCircuitScheme` under `phiTopo`. -/
def samplePrv1Simulator : Prv1Simulator ValidTopo ValidTopo where
  garble t := pure (⟨[], List.replicate t.1.m false⟩, t)
  input _ y := pure y

example {σ : Type} (k : ℕ) (B : PrvSimAdversary ValidCircuit σ) :
    prvSimAdvantage plainCircuitScheme phiTopo k (prv1SimulatorToPrv samplePrv1Simulator) B =
      prv1Advantage plainCircuitScheme phiTopo k samplePrv1Simulator (prvSimToPrv1 B) :=
  prvSimAdvantage_prv1SimulatorToPrv_eq plainCircuitScheme phiTopo k samplePrv1Simulator B

example {σ : Type} (k : ℕ) (A : PrvIndAdversary ValidCircuit σ) :
    prvIndAdvantage plainCircuitScheme phiTopo k A =
      2 * prv1Advantage plainCircuitScheme phiTopo k samplePrv1Simulator
        (prvSimToPrv1 (prvIndToSim plainCircuitScheme phiTopo A)) :=
  prvIndAdvantage_eq_two_mul_prv1Advantage plainCircuitScheme phiTopo
    (phiTopo_compatible plainCircuitScheme_isCircuitScheme) k samplePrv1Simulator A

/-- info: 'Cslib.Crypto.Garbling.phiTopo_isInverter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms phiTopo_isInverter

/-- info: 'Cslib.Crypto.Garbling.phiSize_isInverter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms phiSize_isInverter

/-- info: 'Cslib.Crypto.Garbling.phiCirc_isInverter' does not depend on any axioms -/
#guard_msgs in
#print axioms phiCirc_isInverter

/--
info: 'Cslib.Crypto.Garbling.phiTopo_isEvInverter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms phiTopo_isEvInverter

/--
info: 'Cslib.Crypto.Garbling.phiSize_isEvInverter' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms phiSize_isEvInverter

end CslibFrontierTests.Crypto.GarblingInverters
