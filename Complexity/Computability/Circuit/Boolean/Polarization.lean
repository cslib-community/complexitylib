/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Comparison
public import Complexity.Computability.Circuit.Boolean.Parity
public import Complexity.Computability.Circuit.OutputDistribution
public import Complexity.Probability.StatisticalDistance.Polarization
public import Complexity.Probability.StatisticalDistance.XORSampling
import Complexity.Probability.PMF
import Complexity.Probability.StatisticalDistance.Event

/-!
# Polarization of circuit samplers

The Polarization Lemma of Sahai and Vadhan [SahaiVadhan2003, Lemma 3.3] acts on pairs of circuits:
from De Morgan circuits `C₀` and `C₁` with `n` inputs and `m` outputs it builds circuits whose
output distributions are the polarized pair `Cslib.Probability.PMF.polarize` of the output
distributions of `C₀` and `C₁`, up to the flattening of tuples of outputs into one bit string.

The XOR construction on `j + 1` coordinates (`xorMixCircuit C₀ C₁ j c`) reads `j` selector bits
`r` and `j + 1` blocks of `n` data bits. A chain of exclusive-or gadgets computes the last
selector `c ⊕ parity r`, completing `r` to `BitString.parityComplete c r` (`xorMixStage`).
Coordinate `i` then runs `C₁` or `C₀` on data block `i` according to selector bit `i`, through a
multiplexer (`xorMixBlock`). On uniform inputs the selectors are uniform among the strings of
parity `c` and the data blocks are independent uniform seeds, so the output distribution is the XOR
construction `xorMix` (`outputDist_xorMixCircuit`). Independent copies are `Circuit.replicate`
(`Circuit.outputDist_replicate`), and the polarization construction alternates the two
(`polarizeCircuit`, `outputDist_polarizeCircuit`). Flattening is injective, so the polarized
circuits are exactly as far apart as the polarized distributions
(`dist_outputDist_polarizeCircuit`).

The numbers of coordinates are passed as predecessors, `lam` for `lam + 1` inner coordinates and
`k` for `k + 1` outer coordinates. The XOR construction needs at least one coordinate, and this
keeps the circuit types free of subtraction. Every circuit here has an explicit structure. Their
codes are generated in polynomial time by `Boolean.Polarization.PolyTime`
(`computableInPolyTime_polarizeCode`); their sizes are not stated separately.

## Main definitions

* `Cslib.Circuits.Boolean.xorChainProgram`: a chain of exclusive-or gadgets computing
  `c ⊕ parity (x ∘ sel)`.
* `Cslib.Circuits.Boolean.xorMixStage`: completes the selector bits and routes them to the data
  blocks.
* `Cslib.Circuits.Boolean.xorMixBlock`: one coordinate of the XOR construction.
* `Cslib.Circuits.Boolean.xorMixCircuit`: the XOR construction on circuits.
* `Cslib.Circuits.Boolean.polarizeCircuit`: the polarization construction on circuits.
* `Cslib.Circuits.Boolean.polarizeEquiv`: flattening of the polarized outputs.

## Main results

* `Cslib.Circuits.Boolean.eval_xorMixCircuit`: coordinate `i` evaluates `C₁` or `C₀` on data
  block `i`, according to bit `i` of the completed selector.
* `Cslib.Circuits.Boolean.outputDist_xorMixCircuit`: the output distribution is the XOR
  construction of the output distributions.
* `Cslib.Circuits.Boolean.outputDist_polarizeCircuit`: the output distribution is the polarized
  pair of the output distributions.
* `Cslib.Circuits.Boolean.dist_outputDist_polarizeCircuit`: the polarized circuits are as far
  apart as the polarized distributions.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Cslib.Probability.PMF

/-- A De Morgan program whose last gate computes `c ⊕ x (sel 0) ⊕ ⋯ ⊕ x (sel (j - 1))`: a constant
gate followed by `j` exclusive-or gadgets. Unlike `parityProgram`, it reads arbitrary inputs, folds
in a constant, and handles `j = 0`. -/
def xorChainProgram {N : ℕ} (c : Bool) : (j : ℕ) → (Fin j → Fin N) →
    Program signature N (4 * j + 1)
  | 0, _ => Program.empty.gate ⟨.const c, Fin.elim0⟩
  | j + 1, sel =>
    (xorChainProgram c j (sel ∘ Fin.castSucc)).appendXor (.gate (Fin.last _))
      (.input (sel (Fin.last j)))

/-- The last gate of `xorChainProgram c j sel` computes `c ⊕ parity (x ∘ sel)`. -/
theorem trace_xorChainProgram {N : ℕ} (c : Bool) (j : ℕ) (sel : Fin j → Fin N)
    (x : BitString N) :
    (xorChainProgram c j sel).trace interpretation x (.gate (Fin.last _)) =
      (c ^^ parity j (x ∘ sel)) := by
  induction j with
  | zero =>
    have h : parity 0 (x ∘ sel) = false := by simp [parity, parityOn]
    rw [h, Bool.xor_false]
    exact (Program.eval_gate_last _ _ interpretation x).trans rfl
  | succ j ih =>
    refine (Program.trace_appendXor _ _ _ x).trans ?_
    rw [ih, Program.trace_input, ← Fin.snoc_init_self (x ∘ sel), parity_snoc, Bool.xor_assoc]
    rfl

/-- The wire feeding bit `t` of output block `i` of the selection stage: at `t = 0`, selector
input `i` for `i < j` and the last gate of the chain for `i = j`; at `t = t' + 1`, bit `t'` of data
block `i`. -/
def xorMixStageWire (j n : ℕ) (i : Fin (j + 1)) (t : Fin (n + 1)) :
    Wire (j + (j + 1) * n) (4 * j + 1) :=
  Fin.cases (Fin.lastCases (.gate (Fin.last _)) (fun i' => .input (Fin.castAdd _ i')) i)
    (fun t' => .input (Fin.natAdd j (finProdFinEquiv (i, t')))) t

/-- The selection stage of the XOR construction: from `j` selector bits `r` and `j + 1` data
blocks of `n` bits, output `j + 1` blocks of `n + 1` bits, block `i` being bit `i` of
`BitString.parityComplete c r` followed by data block `i`. -/
def xorMixStage (c : Bool) (j n : ℕ) : Circuit signature (j + (j + 1) * n) ((j + 1) * (n + 1)) :=
  ⟨xorChainProgram c j (Fin.castAdd _), fun o =>
    xorMixStageWire j n (finProdFinEquiv.symm o).1 (finProdFinEquiv.symm o).2⟩

/-- Block `i` of the output of the selection stage is bit `i` of the completed selector followed
by data block `i`. -/
theorem block_eval_xorMixStage (c : Bool) {j n : ℕ} (r : BitString j)
    (d : Fin (j + 1) → BitString n) :
    BitString.block ((xorMixStage c j n).eval interpretation
        (Fin.append r (BitString.blocksEquiv.symm d))) =
      fun i => Fin.cons (BitString.parityComplete c r i) (d i) := by
  funext i t
  rw [BitString.block_apply]
  simp only [Circuit.eval, xorMixStage, Function.comp_apply, Equiv.symm_apply_apply]
  induction t using Fin.cases with
  | zero =>
    rw [Fin.cons_zero]
    induction i using Fin.lastCases with
    | last =>
      simp only [xorMixStageWire, Fin.cases_zero, Fin.lastCases_last]
      rw [trace_xorChainProgram, BitString.parityComplete, Fin.snoc_last]
      congr 2
      funext a
      simp
    | cast i' =>
      simp [xorMixStageWire, BitString.parityComplete]
  | succ t' =>
    simp [xorMixStageWire]

/-- One coordinate of the XOR construction: on a selector bit `b` followed by `n` data bits `y`,
output `C₁ y` if `b` holds and `C₀ y` otherwise, through `muxCircuit`. -/
def xorMixBlock {n m : ℕ} (C₀ C₁ : Circuit signature n m) : Circuit signature (n + 1) m :=
  (muxCircuit m).comp ((Circuit.wiring signature fun _ : Fin 1 => (0 : Fin (n + 1))).append
    ((C₁.comp (Circuit.wiring signature Fin.succ)).append
      (C₀.comp (Circuit.wiring signature Fin.succ))))

/-- `xorMixBlock C₀ C₁` runs `C₁` or `C₀` on the data bits according to the selector bit. -/
theorem eval_xorMixBlock {n m : ℕ} (C₀ C₁ : Circuit signature n m) (b : Bool) (y : BitString n) :
    (xorMixBlock C₀ C₁).eval interpretation (Fin.cons b y) =
      bif b then C₁.eval interpretation y else C₀.eval interpretation y := by
  have h₁ : (Fin.cons b y : BitString (n + 1)) ∘ Fin.succ = y := by
    funext t
    simp
  have h₂ : (Fin.cons b y : BitString (n + 1)) ∘ (fun _ : Fin 1 => (0 : Fin (n + 1))) =
      fun _ => b := by
    funext t
    simp
  simp only [xorMixBlock, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring, h₁, h₂,
    eval_muxCircuit]
  cases b <;> rfl

/-- **The XOR construction on circuits** [SahaiVadhan2003, Lemma 3.5], on `j + 1` coordinates: the
inputs are `j` selector bits followed by `j + 1` consecutive blocks of `n` data bits, and output
block `i` is `C₁` or `C₀` on data block `i`, according to bit `i` of the selector completed to
parity `c`. -/
def xorMixCircuit {n m : ℕ} (C₀ C₁ : Circuit signature n m) (j : ℕ) (c : Bool) :
    Circuit signature (j + (j + 1) * n) ((j + 1) * m) :=
  ((xorMixBlock C₀ C₁).replicate (j + 1)).comp (xorMixStage c j n)

/-- Output block `i` of `xorMixCircuit C₀ C₁ j c` on selector bits `r` and data blocks `d` is
`C₁ (d i)` or `C₀ (d i)`, according to bit `i` of `BitString.parityComplete c r`. -/
theorem eval_xorMixCircuit {n m : ℕ} (C₀ C₁ : Circuit signature n m) (j : ℕ) (c : Bool)
    (r : BitString j) (d : Fin (j + 1) → BitString n) :
    BitString.block ((xorMixCircuit C₀ C₁ j c).eval interpretation
        (Fin.append r (BitString.blocksEquiv.symm d))) =
      fun i => bif BitString.parityComplete c r i then C₁.eval interpretation (d i)
        else C₀.eval interpretation (d i) := by
  rw [xorMixCircuit, Circuit.eval_comp, Circuit.eval_replicate, block_blockMap,
    block_eval_xorMixStage]
  funext i
  exact eval_xorMixBlock C₀ C₁ _ _

/-- **The XOR construction on circuits samples the XOR construction** of the output distributions
of `C₀` and `C₁`, with the `j + 1` output blocks flattened by `Cslib.BitString.blocksEquiv`. -/
theorem outputDist_xorMixCircuit {n m : ℕ} (C₀ C₁ : Circuit signature n m) (j : ℕ) (c : Bool) :
    (xorMixCircuit C₀ C₁ j c).outputDist interpretation =
      (xorMix (C₀.outputDist interpretation) (C₁.outputDist interpretation) (j + 1) c).map
        (BitString.blocksEquiv (m := j + 1) (k := m) (α := Bool)).symm := by
  rw [Circuit.outputDist, Circuit.outputDist, Circuit.outputDist, xorMix_map_uniform,
    PMF.map_comp, ← uniformOfFintype_map_equiv
      ((Equiv.prodCongr (Equiv.refl _)
        (BitString.blocksEquiv (m := j + 1) (k := n) (α := Bool)).symm).trans
        (Fin.appendEquiv j ((j + 1) * n))), PMF.map_comp]
  congr 1
  funext p
  obtain ⟨r, d⟩ := p
  apply BitString.blocksEquiv.injective
  have happ : (Fin.appendEquiv j ((j + 1) * n)) (r, BitString.blocksEquiv.symm d) =
      Fin.append r (BitString.blocksEquiv.symm d) :=
    rfl
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id, Equiv.apply_symm_apply, BitString.blocksEquiv_apply, happ]
  exact eval_xorMixCircuit C₀ C₁ j c r d

/-- **The polarization construction on circuits** [SahaiVadhan2003, proof of Lemma 3.3]: the XOR
construction on `k + 1` coordinates applied to `ell` independent copies of the XOR construction on
`lam + 1` coordinates. -/
def polarizeCircuit {n m : ℕ} (C₀ C₁ : Circuit signature n m) (lam ell k : ℕ) (c : Bool) :
    Circuit signature (k + (k + 1) * (ell * (lam + (lam + 1) * n)))
      ((k + 1) * (ell * ((lam + 1) * m))) :=
  xorMixCircuit ((xorMixCircuit C₀ C₁ lam false).replicate ell)
    ((xorMixCircuit C₀ C₁ lam true).replicate ell) k c

/-- The flattening of `K × ell × L` outputs of `m` bits into one bit string, in consecutive
blocks. -/
def polarizeEquiv (K ell L m : ℕ) :
    (Fin K → Fin ell → Fin L → BitString m) ≃ BitString (K * (ell * (L * m))) :=
  (Equiv.piCongrRight fun _ =>
      (Equiv.piCongrRight fun _ => (BitString.blocksEquiv (m := L) (k := m)).symm).trans
        (BitString.blocksEquiv (m := ell)).symm).trans
    (BitString.blocksEquiv (m := K)).symm

/-- **The polarization construction on circuits samples the polarized pair** of the output
distributions of `C₀` and `C₁`, flattened by `polarizeEquiv`. -/
theorem outputDist_polarizeCircuit {n m : ℕ} (C₀ C₁ : Circuit signature n m) (lam ell k : ℕ)
    (c : Bool) :
    (polarizeCircuit C₀ C₁ lam ell k c).outputDist interpretation =
      (polarize (C₀.outputDist interpretation) (C₁.outputDist interpretation) (lam + 1) ell
        (k + 1) c).map (polarizeEquiv (k + 1) ell (lam + 1) m) := by
  rw [polarizeCircuit, outputDist_xorMixCircuit, Circuit.outputDist_replicate,
    Circuit.outputDist_replicate, outputDist_xorMixCircuit, outputDist_xorMixCircuit, iid_map,
    iid_map, PMF.map_comp, PMF.map_comp, xorMix_map, PMF.map_comp, polarize]
  rfl

/-- **The polarized circuits are as far apart as the polarized distributions** of the output
distributions of `C₀` and `C₁`, with `lam + 1` inner and `k + 1` outer coordinates. -/
theorem dist_outputDist_polarizeCircuit {n m : ℕ} (C₀ C₁ : Circuit signature n m)
    (lam ell k : ℕ) :
    dist ((polarizeCircuit C₀ C₁ lam ell k false).outputDist interpretation)
        ((polarizeCircuit C₀ C₁ lam ell k true).outputDist interpretation) =
      dist (polarize (C₀.outputDist interpretation) (C₁.outputDist interpretation) (lam + 1) ell
          (k + 1) false)
        (polarize (C₀.outputDist interpretation) (C₁.outputDist interpretation) (lam + 1) ell
          (k + 1) true) := by
  rw [outputDist_polarizeCircuit, outputDist_polarizeCircuit,
    dist_map_of_injective _ _ (polarizeEquiv _ _ _ _).injective]

end Cslib.Circuits.Boolean
