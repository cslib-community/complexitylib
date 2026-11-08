/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CodeReplication
public import Complexity.Computability.Circuit.Boolean.Comparison.PolyTime
public import Complexity.Computability.Circuit.Boolean.Polarization
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native generation of the polarization circuits

Raw code generators for the circuits of the Sahai–Vadhan Polarization Lemma
[SahaiVadhan2003, Lemma 3.3], built in `Boolean.Polarization`: the exclusive-or chain, the selection
stage, one coordinate of the XOR construction, the XOR construction and the polarization
construction. Each agrees exactly with the code of the typed circuit, and each is computable in
polynomial time from the codes of the two input circuits, with the numbers of inputs, outputs,
coordinates and copies in unary. So the map `(C₀, C₁) ↦ polarizeCircuit C₀ C₁ lam ell k c` is
polynomial-time on circuit codes when `lam`, `ell` and `k` are polynomially bounded and computed
in unary (`computableInPolyTime_polarizeCode`).

## Main definitions

* `Cslib.Circuits.Boolean.xorChainCode`: the code of `xorChainProgram` on the first inputs.
* `Cslib.Circuits.Boolean.xorMixStageCode`: the code of `xorMixStage`.
* `Cslib.Circuits.Boolean.xorMixBlockCode`: the code of `xorMixBlock`, from the input codes.
* `Cslib.Circuits.Boolean.xorMixCode`: the code of `xorMixCircuit`, from the input codes.
* `Cslib.Circuits.Boolean.polarizeCode`: the code of `polarizeCircuit`, from the input codes.

## Main results

* `Cslib.Circuits.Boolean.xorMixCode_code`, `Cslib.Circuits.Boolean.polarizeCode_code`: exact
  agreement with the typed circuits.
* `Cslib.Circuits.Boolean.computableInPolyTime_xorMixCode`,
  `Cslib.Circuits.Boolean.computableInPolyTime_polarizeCode`: polynomial-time generation.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The four gates of the exclusive-or gadget `Program.appendXor` number `t` of a chain on `N`
inputs: it reads the last gate `4 t` of the chain so far (wire `N + 4 t`) and input `t`. -/
def xorStepCode (N t : ℕ) : List (Op × List ℕ) :=
  [(.or, [N + 4 * t, t]), (.and, [N + 4 * t, t]), (.not, [N + 4 * t + 2]),
    (.and, [N + 4 * t + 1, N + 4 * t + 3])]

/-- The gates of `xorChainProgram c j sel` on `N` inputs, when `sel` selects inputs
`0, …, j - 1`. -/
def xorChainCode (N : ℕ) (c : Bool) (j : ℕ) : List (Op × List ℕ) :=
  (.const c, []) :: (List.range j).flatMap (xorStepCode N)

theorem xorChainCode_code {N : ℕ} (c : Bool) (j : ℕ) (sel : Fin j → Fin N)
    (hsel : ∀ t, (sel t).val = t) :
    xorChainCode N c j = (xorChainProgram c j sel).code := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [xorChainProgram, Program.appendXor]
    simp only [Program.code_gate, ← ih (sel ∘ Fin.castSucc) (fun t => hsel t.castSucc)]
    simp [xorChainCode, xorStepCode, List.range_succ, Line.code, Wire.toNat, hsel,
      Nat.add_assoc]

/-- The wire feeding bit `t` of output block `i` of `xorMixStage c j n`, as a number. -/
def xorMixStageWireCode (j n i t : ℕ) : ℕ :=
  if t < 1 then (if i < j then i else j + (j + 1) * n + 4 * j) else j + (n * i + (t - 1))

/-- The code of the selection stage `xorMixStage c j n`. -/
def xorMixStageCode (c : Bool) (j n : ℕ) : List (Op × List ℕ) × List ℕ :=
  (xorChainCode (j + (j + 1) * n) c j,
    (List.range (j + 1)).flatMap fun i => (List.range (n + 1)).map (xorMixStageWireCode j n i))

private theorem ofFn_eq_map_range {α : Type*} {k : ℕ} (f : Fin k → α) (g : ℕ → α)
    (h : ∀ i : Fin k, f i = g i) : List.ofFn f = (List.range k).map g :=
  List.ext_getElem (by simp) fun i h₁ _ => by
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    exact h _

private theorem ofFn_comp_finProdFinEquiv_symm {α : Type*} {a b : ℕ}
    (g : Fin a × Fin b → α) :
    List.ofFn (fun o => g (finProdFinEquiv.symm o)) =
      (List.ofFn fun i => List.ofFn fun t => g (i, t)).flatten := by
  rw [List.ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i =>
    congrArg List.ofFn (funext fun t => congrArg g ?_)))
  rw [Equiv.symm_apply_eq]
  ext
  simp only [finProdFinEquiv_apply_val]
  ring

theorem xorMixStageCode_code (c : Bool) (j n : ℕ) :
    xorMixStageCode c j n = (xorMixStage c j n).code := by
  refine Prod.ext (xorChainCode_code c j _ fun _ => rfl) ?_
  refine Eq.trans ?_ (ofFn_comp_finProdFinEquiv_symm
    (fun p : Fin (j + 1) × Fin (n + 1) => (xorMixStageWire j n p.1 p.2).toNat)).symm
  simp only [xorMixStageCode]
  rw [List.flatMap_def]
  congr 1
  symm
  refine ofFn_eq_map_range _ _ fun i => ofFn_eq_map_range _ _ fun t => ?_
  induction t using Fin.cases with
  | zero =>
    induction i using Fin.lastCases with
    | last => simp [xorMixStageWire, xorMixStageWireCode, Wire.toNat]
    | cast i => simp [xorMixStageWire, xorMixStageWireCode, Wire.toNat]
  | succ t =>
    simp [xorMixStageWire, xorMixStageWireCode, Wire.toNat]
    omega

/-- The code of one coordinate `xorMixBlock C₀ C₁` of the XOR construction, from the codes `c₀`
and `c₁` of circuits with `n` inputs and `m` outputs. -/
def xorMixBlockCode (n m : ℕ) (c₀ c₁ : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  compCode (n + 1) (muxCode m) (appendCode (n + 1) ([], [0])
    (appendCode (n + 1) (compCode (n + 1) c₁ ([], (List.range n).map (· + 1)))
      (compCode (n + 1) c₀ ([], (List.range n).map (· + 1)))))

theorem xorMixBlockCode_code {n m : ℕ} (C₀ C₁ : Circuit signature n m) :
    xorMixBlockCode n m C₀.code C₁.code = (xorMixBlock C₀ C₁).code := by
  rw [xorMixBlockCode, muxCode_code,
    ← Circuit.code_wiring_eq_map (σ := signature) (f := (Fin.succ : Fin n → Fin (n + 1)))
      (g := (· + 1)) (fun _ => rfl),
    show (([], [0]) : List (Op × List ℕ) × List ℕ) =
      (Circuit.wiring signature fun _ : Fin 1 => (0 : Fin (n + 1))).code from rfl,
    compCode_code, compCode_code, appendCode_code, appendCode_code, compCode_code]
  rfl

/-- The code of the XOR construction `xorMixCircuit C₀ C₁ j c`, from the codes `c₀` and `c₁` of
circuits with `n` inputs and `m` outputs. -/
def xorMixCode (n m j : ℕ) (c : Bool) (c₀ c₁ : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  compCode (j + (j + 1) * n) (replicateCode (n + 1) (j + 1) (xorMixBlockCode n m c₀ c₁))
    (xorMixStageCode c j n)

theorem xorMixCode_code {n m : ℕ} (C₀ C₁ : Circuit signature n m) (j : ℕ) (c : Bool) :
    xorMixCode n m j c C₀.code C₁.code = (xorMixCircuit C₀ C₁ j c).code := by
  rw [xorMixCode, xorMixBlockCode_code, replicateCode_code, xorMixStageCode_code,
    compCode_code]
  rfl

/-- The code of the polarization construction `polarizeCircuit C₀ C₁ lam ell k c`, from the codes
`c₀` and `c₁` of circuits with `n` inputs and `m` outputs. -/
def polarizeCode (n m lam ell k : ℕ) (c : Bool) (c₀ c₁ : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  xorMixCode (ell * (lam + (lam + 1) * n)) (ell * ((lam + 1) * m)) k c
    (replicateCode (lam + (lam + 1) * n) ell (xorMixCode n m lam false c₀ c₁))
    (replicateCode (lam + (lam + 1) * n) ell (xorMixCode n m lam true c₀ c₁))

theorem polarizeCode_code {n m : ℕ} (C₀ C₁ : Circuit signature n m) (lam ell k : ℕ)
    (c : Bool) :
    polarizeCode n m lam ell k c C₀.code C₁.code = (polarizeCircuit C₀ C₁ lam ell k c).code := by
  rw [polarizeCode, xorMixCode_code, xorMixCode_code, replicateCode_code, replicateCode_code,
    xorMixCode_code]
  rfl

open Turing.MultiTapeTM ComputableInPolyTime

/-- The exclusive-or chain is polynomial-time, with a binary input count and a unary length. -/
theorem computableInPolyTime_xorChainCode {α : Type} {enc : α ↪ List Bool} (c : Bool)
    {N j : α → ℕ} (hN : ComputableInPolyTime N enc encNat)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a => xorChainCode (N a) c (j a)) enc (encList encGate) := by
  have hstep : ComputableInPolyTime (fun p : α × ℕ => xorStepCode (N p.1) p.2)
      (encPair enc encUnary) (encList encGate) := by
    have hN' := hN.comp (fst enc encUnary)
    have ht := unary_to_binary.comp (snd enc encUnary)
    unfold xorStepCode
    fun_prop
  exact (const _).cons' (flatMapWithInput (range.comp hj) hstep)

/-- The selection stage is polynomial-time in unary parameters. -/
theorem computableInPolyTime_xorMixStageCode {α : Type} {enc : α ↪ List Bool} (c : Bool)
    {j n : α → ℕ} (hj : ComputableInPolyTime j enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun a => xorMixStageCode c (j a) (n a)) enc encCode := by
  have hjb := unary_to_binary.comp hj
  have hnb := unary_to_binary.comp hn
  have hN : ComputableInPolyTime (fun a => j a + (j a + 1) * n a) enc encNat := by fun_prop
  have hwire : ComputableInPolyTime
      (fun p : (α × ℕ) × ℕ => xorMixStageWireCode (j p.1.1) (n p.1.1) p.1.2 p.2)
      (encPair (encPair enc encUnary) encUnary) encNat := by
    have hj' := hjb.comp ((fst enc encUnary).comp (fst (encPair enc encUnary) encUnary))
    have hn' := hnb.comp ((fst enc encUnary).comp (fst (encPair enc encUnary) encUnary))
    have hi := unary_to_binary.comp ((snd enc encUnary).comp (fst _ encUnary))
    have ht := unary_to_binary.comp (snd (encPair enc encUnary) encUnary)
    unfold xorMixStageWireCode
    fun_prop
  have hrow : ComputableInPolyTime
      (fun p : α × ℕ => (List.range (n p.1 + 1)).map (xorMixStageWireCode (j p.1) (n p.1) p.2))
      (encPair enc encUnary) (encList encNat) := by
    have hn1 : ComputableInPolyTime (fun p : α × ℕ => n p.1 + 1) (encPair enc encUnary)
        encUnary := by
      have := hn.comp (fst enc encUnary)
      fun_prop
    exact mapWithInput (range.comp hn1) hwire
  have hj1 : ComputableInPolyTime (fun a => j a + 1) enc encUnary := by fun_prop
  exact (computableInPolyTime_xorChainCode c hN hj).prod (flatMapWithInput (range.comp hj1) hrow)

/-- One coordinate of the XOR construction is polynomial-time in unary sizes and the codes. -/
theorem computableInPolyTime_xorMixBlockCode {α : Type} {enc : α ↪ List Bool}
    {n m : α → ℕ} {c₀ c₁ : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (hc₀ : ComputableInPolyTime c₀ enc encCode) (hc₁ : ComputableInPolyTime c₁ enc encCode) :
    ComputableInPolyTime (fun a => xorMixBlockCode (n a) (m a) (c₀ a) (c₁ a)) enc encCode := by
  have hnb := unary_to_binary.comp hn
  have hn1 : ComputableInPolyTime (fun a => n a + 1) enc encNat := by fun_prop
  have hsucc : ComputableInPolyTime
      (fun a => (([] : List (Op × List ℕ)), (List.range (n a)).map (· + 1))) enc encCode := by
    have hi : ComputableInPolyTime (fun p : α × ℕ => p.2 + 1) (encPair enc encUnary) encNat := by
      have := unary_to_binary.comp (snd enc encUnary)
      fun_prop
    exact (const []).prod (mapWithInput (range.comp hn) hi)
  exact computableInPolyTime_compCode hn1 (computableInPolyTime_muxCode.comp hm)
    (computableInPolyTime_appendCode hn1 (const _)
      (computableInPolyTime_appendCode hn1 (computableInPolyTime_compCode hn1 hc₁ hsucc)
        (computableInPolyTime_compCode hn1 hc₀ hsucc)))

/-- The XOR construction is polynomial-time in unary sizes and the codes. -/
theorem computableInPolyTime_xorMixCode {α : Type} {enc : α ↪ List Bool} (c : Bool)
    {n m j : α → ℕ} {c₀ c₁ : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary)
    (hc₀ : ComputableInPolyTime c₀ enc encCode) (hc₁ : ComputableInPolyTime c₁ enc encCode) :
    ComputableInPolyTime (fun a => xorMixCode (n a) (m a) (j a) c (c₀ a) (c₁ a)) enc encCode := by
  have hnb := unary_to_binary.comp hn
  have hjb := unary_to_binary.comp hj
  have hN : ComputableInPolyTime (fun a => j a + (j a + 1) * n a) enc encNat := by fun_prop
  have hn1 : ComputableInPolyTime (fun a => n a + 1) enc encNat := by fun_prop
  have hj1 : ComputableInPolyTime (fun a => j a + 1) enc encUnary := by fun_prop
  exact computableInPolyTime_compCode hN
    (computableInPolyTime_replicateCode hn1 hj1
      (computableInPolyTime_xorMixBlockCode hn hm hc₀ hc₁))
    (computableInPolyTime_xorMixStageCode c hj hn)

/-- The polarization construction is polynomial-time in unary sizes and parameters and the codes.
-/
theorem computableInPolyTime_polarizeCode {α : Type} {enc : α ↪ List Bool} (c : Bool)
    {n m lam ell k : α → ℕ} {c₀ c₁ : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (hlam : ComputableInPolyTime lam enc encUnary) (hell : ComputableInPolyTime ell enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hc₀ : ComputableInPolyTime c₀ enc encCode) (hc₁ : ComputableInPolyTime c₁ enc encCode) :
    ComputableInPolyTime
      (fun a => polarizeCode (n a) (m a) (lam a) (ell a) (k a) c (c₀ a) (c₁ a)) enc encCode := by
  have hin : ComputableInPolyTime (fun a => lam a + (lam a + 1) * n a) enc encUnary := by
    fun_prop
  have hinb := unary_to_binary.comp hin
  have hN : ComputableInPolyTime (fun a => ell a * (lam a + (lam a + 1) * n a)) enc encUnary := by
    fun_prop
  have hM : ComputableInPolyTime (fun a => ell a * ((lam a + 1) * m a)) enc encUnary := by
    fun_prop
  exact computableInPolyTime_xorMixCode c hN hM hk
    (computableInPolyTime_replicateCode hinb hell
      (computableInPolyTime_xorMixCode false hn hm hlam hc₀ hc₁))
    (computableInPolyTime_replicateCode hinb hell
      (computableInPolyTime_xorMixCode true hn hm hlam hc₀ hc₁))

end Cslib.Circuits.Boolean
