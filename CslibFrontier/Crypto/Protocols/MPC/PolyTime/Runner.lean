/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.PolyTime.Encoding
public import CslibFrontier.Computability.Complexity.Problems.CircuitValue.Compilation
-- `import all`: reads the private view-word layout `gmwViewWord` and encoders `encOTSubCoins`,
-- `encOTOracleAnswers` and `encPairsMsgReceived` that the word-level runners emit.
import all CslibFrontier.Crypto.Protocols.MPC.PolyTime.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Probabilistic.Fold
import CslibFrontier.Computability.Probabilistic.Finite
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Word-Level GMW Runners and Their Efficiency Certificates

Proof infrastructure for the uniform efficiency certificates of
`Cslib.Crypto.Protocols.MPC.PolyTime`. It compiles `xorPreludeCircuit` uniformly in polynomial
time, defines the word-level real runner `PolyTimeRunner.realRunWord` and simulator
`PolyTimeRunner.simRunWord` of the $\text{OT}_1^4$-hybrid GMW protocol family stage by stage
(Step 1 input sharing, Step 2 gates through `Step2Acc`, Step 3 output reconstruction through
`Step3Acc`), and proves `IsOraclePPTOn` / `IsPPTOn` for them. Every declaration here is private
proof plumbing. `Cslib.Crypto.Protocols.MPC.PolyTime.InputProgEquiv` and
`Cslib.Crypto.Protocols.MPC.PolyTime.Certificates` read them through `import all`, and the
public certificates are stated in `Certificates`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.2 (Eq. 7.20, p. 640), Section 7.3.3 (Construction 7.3.7, pp. 643–644),
  Section 7.3.4 (Theorem 7.3.11, p. 648), Section 7.5.1.2 (Definition 7.5.1, Eqs. 7.39–7.40,
  p. 696; p. 697), Section 7.5.2.1 (p. 703), Section 7.5.2.2 (Construction 7.5.8, p. 704),
  Section 7.5.2.3 (Construction 7.5.10, p. 706), and Section 7.5.2.4 (Theorem 7.5.12, p. 707).
-/

-- This proof-only stage is intentionally private; later stages import all.
set_option linter.privateModule false

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp Cslib.Circuits Turing.MultiTapeTM

/-! ### Part 3: Uniform Polynomial-Time Compilation of `xorPreludeCircuit` -/

namespace XORPreludeCode

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Raw circuit code of `XORPrelude.xorBitAtCircuit coins c`. -/
private def xorBitAtCode (coins c : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  ([(.or, [c, c + coins]),
    (.and, [c, c + coins]),
    (.not, [(coins + coins) + 1]),
    (.and, [coins + coins, (coins + coins) + 2])],
   [(coins + coins) + 3])

private theorem code_xorBitAtCircuit (coins : ℕ) (c : Fin coins) :
    (XORPrelude.xorBitAtCircuit coins c).code = xorBitAtCode coins c.val := by
  simp [XORPrelude.xorBitAtCircuit, Program.appendXor, Circuit.code, Line.code, xorBitAtCode,
    Nat.add_comm]

/-- Raw circuit code of `XORPrelude.zeroBitStringCircuit w coins`. -/
private def zeroBitStringCode (w coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  ([(.const false, [])], List.replicate coins w)

private theorem code_zeroBitStringCircuit (w coins : ℕ) :
    (XORPrelude.zeroBitStringCircuit w coins).code = zeroBitStringCode w coins := by
  simp [XORPrelude.zeroBitStringCircuit, Circuit.code, Line.code, zeroBitStringCode]

/-- Raw circuit code of `XORPrelude.xorBitStringsCircuit coins`. -/
private def xorBitStringsCode (coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  bundleCode (coins + coins) 4 ((List.range coins).map (xorBitAtCode coins))

private theorem code_xorBitStringsCircuit (coins : ℕ) :
    (XORPrelude.xorBitStringsCircuit coins).code = xorBitStringsCode coins := by
  have hmap : (List.range coins).map (xorBitAtCode coins) =
      List.ofFn (fun c : Fin coins => (XORPrelude.xorBitAtCircuit coins c).code) := by
    refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
    simp [code_xorBitAtCircuit]
  rw [XORPrelude.xorBitStringsCircuit, xorBitStringsCode, hmap,
    bundleCode_code (XORPrelude.xorBitAtCircuit coins) 4 (fun _ => rfl)]

/-- Raw circuit code of `XORPrelude.sumBlocksCircuit m coins`. -/
private def sumBlocksCode : (m coins : ℕ) → List (Boolean.Op × List ℕ) × List ℕ
  | 0, coins => zeroBitStringCode (0 * coins) coins
  | m + 1, coins =>
    compCode ((m + 1) * coins) (xorBitStringsCode coins)
      (appendCode ((m + 1) * coins)
        (compCode ((m + 1) * coins) (sumBlocksCode m coins)
          ([], List.range (m * coins)))
        ([], (List.range coins).map (fun c => c + coins * m)))

private theorem code_sumBlocksCircuit (m coins : ℕ) :
    (XORPrelude.sumBlocksCircuit m coins).code = sumBlocksCode m coins := by
  induction m with
  | zero =>
    simpa [XORPrelude.sumBlocksCircuit, sumBlocksCode] using
      code_zeroBitStringCircuit (0 * coins) coins
  | succ m ih =>
    have hw₁ :
        (Circuit.wiring Boolean.signature
          (Fin.castLE (Nat.mul_le_mul_right coins (Nat.le_succ m)))).code =
        ([], List.range (m * coins)) := by
      simpa using Circuit.code_wiring_eq_map (σ := Boolean.signature)
        (f := Fin.castLE (Nat.mul_le_mul_right coins (Nat.le_succ m))) (g := id) fun _ => rfl
    have hw₂ :
        (Circuit.wiring Boolean.signature
          (fun c : Fin coins => finProdFinEquiv (Fin.last m, c))).code =
        ([], (List.range coins).map (fun c => c + coins * m)) :=
      Circuit.code_wiring_eq_map fun c => by simp [finProdFinEquiv_apply_val]
    simp only [XORPrelude.sumBlocksCircuit, sumBlocksCode, ← compCode_code, ← appendCode_code,
      code_xorBitStringsCircuit, ih, hw₁, hw₂]

/-- Raw circuit code of a `m * width`-output wiring picking strided slices of width `width` at
offset `offset` with block stride `stride`. -/
private def extractSliceCode (m stride offset width : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  ([], (List.range (m * width)).map fun idx => (offset + idx % width) + stride * (idx / width))

/-- Raw circuit code of `XORPrelude.extractInputsCircuit m n coins`. -/
private def extractInputsCode (m n coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  extractSliceCode m (n + coins) 0 n

private theorem code_extractInputsCircuit (m n coins : ℕ) :
    (XORPrelude.extractInputsCircuit m n coins).code = extractInputsCode m n coins :=
  Circuit.code_wiring_eq_map fun idx => by
    simp [finProdFinEquiv_apply_val, finProdFinEquiv_symm_apply]

/-- Raw circuit code of `XORPrelude.extractCoinsCircuit m n coins`. -/
private def extractCoinsCode (m n coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  extractSliceCode m (n + coins) n coins

private theorem code_extractCoinsCircuit (m n coins : ℕ) :
    (XORPrelude.extractCoinsCircuit m n coins).code = extractCoinsCode m n coins :=
  Circuit.code_wiring_eq_map fun idx => by
    simp [finProdFinEquiv_apply_val, finProdFinEquiv_symm_apply]

/-- Raw circuit code of `xorPreludeCircuit m n coins`. -/
private def xorPreludeCode (m n coins : ℕ) : List (Boolean.Op × List ℕ) × List ℕ :=
  appendCode (m * (n + coins))
    (extractInputsCode m n coins)
    (compCode (m * (n + coins)) (sumBlocksCode m coins) (extractCoinsCode m n coins))

private theorem code_xorPreludeCircuit (m n coins : ℕ) :
    (xorPreludeCircuit m n coins).code = xorPreludeCode m n coins := by
  simp only [xorPreludeCircuit, xorPreludeCode, ← appendCode_code, ← compCode_code,
    code_extractInputsCircuit, code_sumBlocksCircuit, code_extractCoinsCircuit]

private theorem computableTidilyInPolyTime_xorBitAtCode {α : Type} {enc : α ↪ List Bool}
    {coins c : α → ℕ}
    (hcoins : ComputableTidilyInPolyTime coins enc encNat)
    (hc : ComputableTidilyInPolyTime c enc encNat) :
    ComputableTidilyInPolyTime (fun a => xorBitAtCode (coins a) (c a)) enc encCode := by
  unfold xorBitAtCode
  fun_prop

private theorem computableTidilyInPolyTime_zeroBitStringCode {α : Type} {enc : α ↪ List Bool}
    {w coins : α → ℕ}
    (hw : ComputableTidilyInPolyTime w enc encNat)
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => zeroBitStringCode (w a) (coins a)) enc encCode := by
  unfold zeroBitStringCode
  fun_prop

private theorem computableTidilyInPolyTime_xorBitStringsCode {α : Type} {enc : α ↪ List Bool}
    {coins : α → ℕ}
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => xorBitStringsCode (coins a)) enc encCode := by
  have hcoinsBin : ComputableTidilyInPolyTime coins enc encNat := unary_to_binary.comp hcoins
  have htwoCoins : ComputableTidilyInPolyTime (fun a => coins a + coins a) enc encNat := by
    fun_prop
  have hbit : ComputableTidilyInPolyTime
      (fun p : α × ℕ => xorBitAtCode (coins p.1) p.2)
      (encPair enc encUnary) encCode :=
    computableTidilyInPolyTime_xorBitAtCode
      (hcoinsBin.comp (fst enc encUnary))
      (unary_to_binary.comp (snd enc encUnary))
  exact (computableInPolyTime_bundleCode (.of_tidy htwoCoins) (.of_tidy (const 4))
    (.of_tidy (mapWith hbit id' (range.comp hcoins)))).tidy

private theorem computableTidilyInPolyTime_sumBlocksCode {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {coins : α → ℕ}
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => sumBlocksCode m (coins a)) enc encCode := by
  induction m with
  | zero =>
    have hcoinsBin := unary_to_binary.comp hcoins
    have hw := binary_mul' (const 0) hcoinsBin
    exact computableTidilyInPolyTime_zeroBitStringCode hw hcoins
  | succ m ih =>
    have hcoinsBin := unary_to_binary.comp hcoins
    have hmCoinsUnary := unary_mul.comp ((const m).prod hcoins)
    have hsuccCoinsBin := binary_mul' (const (m + 1)) hcoinsBin
    have hrange₁ : ComputableTidilyInPolyTime
        (fun a => ([], List.range (m * coins a))) enc encCode := by
      have hr : ComputableTidilyInPolyTime
          (fun a => List.range (m * coins a)) enc (encList encNat) := by
        simpa only [Function.comp_def, List.map_id'] using
          unary_to_binary.map.comp (range.comp hmCoinsUnary)
      exact (const []).prod hr
    have hrange₂ : ComputableTidilyInPolyTime
        (fun a => ([], (List.range (coins a)).map (fun c => c + coins a * m))) enc encCode := by
      have hp1 := hcoinsBin.comp (fst enc encUnary)
      have hp2 := unary_to_binary.comp (snd enc encUnary)
      have hf := binary_add' hp2 (binary_mul' hp1 (const m))
      exact (const []).prod (mapWith hf id' (range.comp hcoins))
    exact (computableInPolyTime_compCode (.of_tidy hsuccCoinsBin)
      (.of_tidy (computableTidilyInPolyTime_xorBitStringsCode hcoins))
      (computableInPolyTime_appendCode (.of_tidy hsuccCoinsBin)
        (computableInPolyTime_compCode (.of_tidy hsuccCoinsBin) (.of_tidy ih) (.of_tidy hrange₁))
        (.of_tidy hrange₂))).tidy

private theorem computableTidilyInPolyTime_extractSliceCode {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {stride offset width : α → ℕ}
    (hstride : ComputableTidilyInPolyTime stride enc encNat)
    (hoffset : ComputableTidilyInPolyTime offset enc encNat)
    (hwidth : ComputableTidilyInPolyTime width enc encUnary) :
    ComputableTidilyInPolyTime
      (fun a => extractSliceCode m (stride a) (offset a) (width a)) enc encCode := by
  have hwidthBin := unary_to_binary.comp hwidth
  have hmw := unary_mul.comp ((const m).prod hwidth)
  have hp_stride := hstride.comp (fst enc encUnary)
  have hp_offset := hoffset.comp (fst enc encUnary)
  have hp_width := hwidthBin.comp (fst enc encUnary)
  have hp_idx := unary_to_binary.comp (snd enc encUnary)
  have hmod := ComputableInPolyTime.binary_mod.tidy.comp (hp_idx.prod hp_width)
  have hdiv := ComputableInPolyTime.binary_div.tidy.comp (hp_idx.prod hp_width)
  have hf := binary_add' (binary_add' hp_offset hmod) (binary_mul' hp_stride hdiv)
  exact (const []).prod (mapWith hf id' (range.comp hmw))

private theorem computableTidilyInPolyTime_xorPreludeCode {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {n coins : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hcoins : ComputableTidilyInPolyTime coins enc encUnary) :
    ComputableTidilyInPolyTime (fun a => xorPreludeCode m (n a) (coins a)) enc encCode := by
  have hnBin := unary_to_binary.comp hn
  have hcoinsBin := unary_to_binary.comp hcoins
  have hstride := binary_add' hnBin hcoinsBin
  have hwidth := binary_mul' (const m) hstride
  exact (computableInPolyTime_appendCode (.of_tidy hwidth)
    (.of_tidy (computableTidilyInPolyTime_extractSliceCode m hstride (const 0) hn))
    (computableInPolyTime_compCode (.of_tidy hwidth)
      (.of_tidy (computableTidilyInPolyTime_sumBlocksCode m hcoins))
      (.of_tidy (computableTidilyInPolyTime_extractSliceCode m hstride hnBin hcoins)))).tidy

end XORPreludeCode

/-- The circuit code of `xorPreludeCircuit m (n a) (coins a)` is constructible in uniform
polynomial time from `a : α`. -/
private theorem computableInPolyTime_code_xorPreludeCircuit {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {n coins : α → ℕ}
    (hn : ComputableInPolyTime n enc Turing.MultiTapeTM.encUnary)
    (hcoins : ComputableInPolyTime coins enc Turing.MultiTapeTM.encUnary) :
    ComputableInPolyTime (fun a => (xorPreludeCircuit m (n a) (coins a)).code)
      enc Boolean.encCode :=
  .of_tidy
    ((XORPreludeCode.computableTidilyInPolyTime_xorPreludeCode m hn.tidy hcoins.tidy).of_enc_eq
      fun a => by rw [XORPreludeCode.code_xorPreludeCircuit])

/-- Composing a polynomial-time constructible circuit family `C a` with `xorPreludeCircuit` yields
a polynomial-time constructible circuit family
`(C a).comp (xorPreludeCircuit m (n a) (coins a))`. -/
private theorem computableInPolyTime_code_comp_xorPreludeCircuit {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) {n coins k : α → ℕ}
    {C : (a : α) → Cslib.Circuits.Circuit Boolean.signature (m * n a + coins a) (m * k a)}
    (hn : ComputableInPolyTime n enc Turing.MultiTapeTM.encUnary)
    (hcoins : ComputableInPolyTime coins enc Turing.MultiTapeTM.encUnary)
    (hC : ComputableInPolyTime (fun a => (C a).code) enc Boolean.encCode) :
    ComputableInPolyTime
      (fun a => ((C a).comp (xorPreludeCircuit m (n a) (coins a))).code)
      enc Boolean.encCode := by
  have hnBin : Turing.MultiTapeTM.ComputableTidilyInPolyTime n enc Turing.MultiTapeTM.encNat :=
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary.comp hn.tidy
  have hcoinsBin :
      Turing.MultiTapeTM.ComputableTidilyInPolyTime coins enc Turing.MultiTapeTM.encNat :=
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary.comp hcoins.tidy
  have hwidth : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a => m * (n a + coins a)) enc Turing.MultiTapeTM.encNat := by
    fun_prop
  have hcomp := (Boolean.computableInPolyTime_compCode (.of_tidy hwidth) hC
    (computableInPolyTime_code_xorPreludeCircuit m hn hcoins)).tidy
  exact .of_tidy (hcomp.of_enc_eq fun a => by rw [Boolean.compCode_code])

/-! ### Part 4: Word-Level Efficiency -/

namespace PolyTimeRunner

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

private theorem length_encList_ofFn_le {n : ℕ} (u v : Fin n → List Bool) (d : ℕ)
    (h : ∀ i : Fin n, (v i).length ≤ (u i).length + d) :
    (encList encBits (List.ofFn v)).length ≤
      (encList encBits (List.ofFn u)).length + n * (2 * d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 := h 0
    have hs := ih (fun i => u i.succ) (fun i => v i.succ) (fun i => h i.succ)
    simp only [List.ofFn_succ, encList_cons, List.length_append, length_frame,
      encBits_apply, Nat.add_mul, Nat.one_mul]
    omega

private theorem length_encPi_encBits_le {m : ℕ} (f g : Fin m → List Bool) (d : ℕ)
    (h : ∀ i : Fin m, (g i).length ≤ (f i).length + d) :
    (encPi encBits g).length ≤ (encPi encBits f).length + m * (2 * d) := by
  simpa only [encPi_apply, Fintype.card_fin] using
    length_encList_ofFn_le
      (fun i => f ((Fintype.equivFin (Fin m)).symm i))
      (fun i => g ((Fintype.equivFin (Fin m)).symm i))
      d (fun i => h _)

private theorem computableTidilyInPolyTime_ofList_fin (d : ℕ) :
    ComputableTidilyInPolyTime (Cslib.BitString.ofList d) encBits (encPi encBool) := by
  refine pi fun k => ?_
  change ComputableTidilyInPolyTime
    ((fun p : List Bool × ℕ => p.1.getD p.2 false) ∘ fun w => (w, k.val)) encBits encBool
  exact (listGetD false).comp (id'.prod (const k.val))

/-- Sampling a uniform function `ι → Bool` from any finite index type `[Fintype ι]` is strict PPT
for any fixed input and output encodings. -/
private theorem isPPTOn_uniform_fintype_bool {α ι : Type} [Fintype ι] [DecidableEq ι]
    (input : α ↪ List Bool) (output : (ι → Bool) ↪ List Bool) :
    IsPPTOn input output (fun _ => ProbComp.uniform (ι → Bool)) := by
  let card := Fintype.card ι
  let e : ι ≃ Fin card := Fintype.equivFin ι
  let toMap : (Fin card → Bool) → (ι → Bool) := fun f i => f (e i)
  let decode : List Bool → (ι → Bool) := fun w => toMap (Cslib.BitString.ofList card w)
  have hdecode : ComputableTidilyInPolyTime decode encBits output :=
    (of_finite (encA := encPi encBool) (encB := output) toMap).comp
      (computableTidilyInPolyTime_ofList_fin card)
  have hseeded : IsPPTOn input output (fun _ : α => decode <$> Cslib.BitString.sampleList card) :=
    IsPPTOn.of_seeded (.of_tidy (const card))
      (.of_tidy (hdecode.comp (snd input encBits)))
  refine hseeded.congr fun _ => ?_
  rw [ProbComp.eval_map, Cslib.BitString.eval_sampleList, Cslib.BitString.uniformList,
    PMF.map_comp, ProbComp.eval_uniform]
  have heq : decode ∘ List.ofFn = Equiv.piCongrLeft' (fun _ => Bool) e.symm := by
    funext f
    ext i
    simp [decode, toMap, Cslib.BitString.ofList_ofFn, Equiv.piCongrLeft']
  rw [heq, PMF.uniformOfFintype_map_equiv]

/-- Sampling `m` independent bit lists of polynomial-time unary lengths `len a i` is strict PPT. -/
private theorem isPPTOn_pi_sampleList {α : Type} {input : α ↪ List Bool}
    (m : ℕ) {len : α → Fin m → ℕ}
    (hlen : ∀ i : Fin m, ComputableTidilyInPolyTime (fun a => len a i) input encUnary) :
    IsPPTOn input (encPi encBits)
      (fun a => OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (len a i))) := by
  induction m with
  | zero =>
    have hpure : IsPPTOn input (encPi encBits) (fun _ : α => pure Fin.elim0) :=
      (pi fun i : Fin 0 => i.elim0).isPPTOn
    refine hpure.congr fun a => ?_
    ext f
    simp [Subsingleton.elim f Fin.elim0]
  | succ m ih =>
    have h0 : IsPPTOn input encBits (fun a => Cslib.BitString.sampleList (len a 0)) :=
      (ComputableInPolyTime.of_tidy (hlen 0)).sampleList
    have hrest : IsPPTOn input (encPi encBits)
        (fun a => OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (len a i.succ))) :=
      ih (fun i => hlen i.succ)
    have hcomb : ComputableTidilyInPolyTime
        (fun p : List Bool × (Fin m → List Bool) => Fin.cons p.1 p.2)
        (encPair encBits (encPi encBits)) (encPi encBits) := by
      refine pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact fst _ _
      · exact (pi_apply encBits j).comp (snd _ _)
    have hsecond : IsPPTOn (encPair input encBits) (encPair encBits (encPi encBits))
        (fun pair : α × List Bool =>
          (fun xs => (pair.2, xs)) <$>
            OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (len pair.1 i.succ))) :=
      (hrest.preprocess (.of_tidy (fst input encBits))).pair (snd input encBits)
    have hbind :=
      (h0.bind_with (second := fun a x0 =>
        (fun xs => (x0, xs)) <$>
          OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (len a i.succ)))
        hsecond).map (.of_tidy hcomb)
    refine hbind.congr fun a => ?_
    rw [OracleComp.pi_succ]
    simp [ProbComp.eval_bind, ProbComp.eval_map]

/-! ### Section 4B: Word-Level Real and Simulated Runners and Their PPT Certificates -/

/-- Any family of distributions `fun a => g a <$> ProbComp.uniform (ι → Bool)` over a finite input
type `[Finite α]` and finite coin index type `[Fintype ι]` is strict PPT. -/
private theorem isPPTOn_of_finite_uniform {α β ι : Type} [Finite α] [Fintype ι] [DecidableEq ι]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (g : α → (ι → Bool) → β) :
    IsPPTOn input output (fun a => g a <$> ProbComp.uniform (ι → Bool)) := by
  cases nonempty_fintype α
  have hunif : IsPPTOn input (encFinite (ι → Bool)) (fun _ => ProbComp.uniform (ι → Bool)) :=
    isPPTOn_uniform_fintype_bool input (encFinite (ι → Bool))
  exact hunif.map_with (.of_tidy (of_finite (fun p : α × (ι → Bool) => g p.1 p.2)))

private theorem isPPTOn_sampleAdditiveShares (m : ℕ) :
    IsPPTOn encBool (encFinite (Fin m → Bool)) (ProbComp.sampleAdditiveShares m) :=
  isPPTOn_of_finite_uniform encBool (encFinite (Fin m → Bool)) (ProbComp.completeShares m)

/-- The `N`-bit additive share sent by party `s` to party `i` in Step 1 of `gmwCircuitProtocol`. -/
private def step1SenderShare (m N : ℕ) (xr_s c1_s : List Bool) (i : Fin m) : List Bool :=
  (List.range N).map fun j =>
    ProbComp.completeShares m (xr_s.getD j false)
      (Cslib.BitString.ofList (m - 1) (Cslib.BitString.listRow (m - 1) j c1_s)) i

/-- Initial input-wire list (and Step 1 received share transcript) of party `i` in
`gmwCircuitProtocol`. -/
private def step1Wires (m N : ℕ) (x_bits r_bits c1_bits : Fin m → List Bool) (i : Fin m) :
    List Bool :=
  (List.finRange m).flatMap fun s =>
    step1SenderShare m N (x_bits s ++ r_bits s) (c1_bits s) i

private theorem computableTidilyInPolyTime_step1Wires {α : Type} {input : α ↪ List Bool}
    (m : ℕ) {N : α → ℕ} {x_bits r_bits c1_bits : α → Fin m → List Bool}
    (hN : ComputableTidilyInPolyTime N input encUnary)
    (hx : ComputableTidilyInPolyTime x_bits input (encPi encBits))
    (hr : ComputableTidilyInPolyTime r_bits input (encPi encBits))
    (hc1 : ComputableTidilyInPolyTime c1_bits input (encPi encBits)) :
    ComputableTidilyInPolyTime
      (fun a => step1Wires m (N a) (x_bits a) (r_bits a) (c1_bits a))
      input (encPi encBits) := by
  refine pi fun i => ?_
  have hsender (s : Fin m) :
      ComputableTidilyInPolyTime
        (fun a => step1SenderShare m (N a) (x_bits a s ++ r_bits a s) (c1_bits a s) i)
        input encBits := by
    have hxr := bitsAppend ((pi_apply encBits s).comp hx) ((pi_apply encBits s).comp hr)
    have hc1s := (pi_apply encBits s).comp hc1
    have hbit := bitsGetDWithInput (hxr.comp (fst input encUnary)) (snd input encUnary) false
    have hrow := (computableTidilyInPolyTime_ofList_fin (m - 1)).comp
      (bitsRowWithInput (const (m - 1)) (snd input encUnary) (hc1s.comp (fst input encUnary)))
    have hcomp : ComputableTidilyInPolyTime
        (fun q : Bool × (Fin (m - 1) → Bool) => ProbComp.completeShares m q.1 q.2 i)
        (encPair encBool (encPi encBool)) encBool :=
      of_finite _
    have hbody := hcomp.comp (hbit.prod hrow)
    exact mapToBitsWithInput (range.comp hN) hbody
  simpa only [step1Wires, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    bitsFlatten (mapConst (List.finRange m) fun s _ => hsender s)

/-- One pairwise $\text{OT}_1^4$ invocation in `twoPartyMulProtocol` at pair `p : OrderedPair m`
under `Steps.runEncoded`, returning `(c₀, ans_v) : Bool × Bool`. -/
private noncomputable def realPairCall (m : ℕ) (p : OrderedPair m) (x : Fin m → Bool × Bool) :
    WordOracleComp Unit (Bool × Bool) :=
  ProbOracleComp.sample (ProbComp.uniform Bool) >>= fun c₀ =>
    (fun raw => (c₀, raw.headD false)) <$>
      List.take 1 <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), encodeOT14Query
            (fun s => twoPartyMulQuery s (x (pairEmbedding p s), twoPartyMulCoins c₀ s)))

private theorem isOraclePPTOn_realPairCall (m : ℕ) (p : OrderedPair m) :
    IsOraclePPTOn (encFinite (Fin m → Bool × Bool)) (encPair encBool encBool)
      (realPairCall m p) := by
  refine (IsOraclePPTOn.finite_cases
    (tagEncoding := encFinite (Fin m → Bool × Bool))
    (tag := id) (branch := fun x _ => realPairCall m p x) id' ?_).congr
    fun _ _ _ _ => rfl
  intro x
  unfold realPairCall
  have hc₀ : IsOraclePPTOn (Operation := Unit) (encFinite (Fin m → Bool × Bool)) encBool
      (fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)) := by
    have hbool : IsPPTOn (encFinite (Fin m → Bool × Bool)) encBool
        (fun _ => ProbComp.uniform Bool) := by
      refine (isPPTOn_of_finite_uniform (encFinite (Fin m → Bool × Bool)) encBool
        (fun _ (f : Fin 1 → Bool) => f 0)).congr fun _ => ?_
      rw [ProbComp.eval_map, ProbComp.eval_uniform, ProbComp.eval_uniform]
      exact PMF.uniformOfFintype_map_equiv (Equiv.funUnique (Fin 1) Bool)
    exact hbool.isOraclePPTOn
  have hq : IsOraclePPTOn encBool encBits
      (fun c₀ : Bool =>
        List.take ((fun _ : Bool => 1) c₀) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), encodeOT14Query
              (fun s => twoPartyMulQuery s (x (pairEmbedding p s), twoPartyMulCoins c₀ s)))) :=
    IsOraclePPTOn.query_take () (of_finite _) (const 1)
  have hpost : ComputableTidilyInPolyTime
      (fun q : Bool × List Bool => (q.1, q.2.headD false))
      (encPair encBool encBits) (encPair encBool encBool) :=
    (fst encBool encBits).prod
      (comp' (headD (encA := encBool) (encL := encBits) false) (snd encBool encBits))
  have hsecond := hq.map_with (f := fun c₀ raw => (c₀, raw.headD false)) hpost
  exact hc₀.bind hsecond

/-- Sequential execution of `realPairCall m p x` along `L : List (OrderedPair m)`. -/
private noncomputable def realPairsCalls (m : ℕ) (x : Fin m → Bool × Bool) :
    List (OrderedPair m) → WordOracleComp Unit (OrderedPair m → Bool × Bool)
  | [] => pure (fun _ => (false, false))
  | p :: L =>
    realPairCall m p x >>= fun res =>
      (fun rest => Function.update rest p res) <$> realPairsCalls m x L

private theorem isOraclePPTOn_realPairsCalls (m : ℕ) (L : List (OrderedPair m)) :
    IsOraclePPTOn (encFinite (Fin m → Bool × Bool)) (encFinite (OrderedPair m → Bool × Bool))
      (fun x => realPairsCalls m x L) := by
  induction L with
  | nil =>
    unfold realPairsCalls
    exact ((of_finite (fun _ : Fin m → Bool × Bool =>
      (fun _ : OrderedPair m => (false, false)))).isPPTOn).isOraclePPTOn
  | cons p L ih =>
    unfold realPairsCalls
    have hprep := ih.preprocess (fst (encFinite (Fin m → Bool × Bool)) (encPair encBool encBool))
    have hsecond := hprep.map_with
      (f := fun pair rest => Function.update rest p pair.2)
      (of_finite (encB := encFinite (OrderedPair m → Bool × Bool)) _)
    exact (isOraclePPTOn_realPairCall m p).bind_with
      (second := fun x res =>
        (fun rest => Function.update rest p res) <$> realPairsCalls m x L)
      hsecond

private theorem length_flatten_ite_singleton_le {α : Type} (L : List α)
    (P : α → Prop) [DecidablePred P] (f : α → Bool) :
    ((L.map fun a => if P a then [f a] else []).flatten).length ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.flatten_cons]
    split_ifs <;> (simp only [List.length_append, List.length_cons, List.length_nil]; omega)

/-- Deterministic extraction of `(ans, ot_c_delta, ot_a_delta)` from one `multiPartyMulProtocol m`
invocation given the pair transcript `tr : OrderedPair m → Bool × Bool`. -/
private def realSharedMulPure (m : ℕ) (x : Fin m → Bool × Bool) (tr : OrderedPair m → Bool × Bool) :
    (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool) :=
  (fun i =>
    m • ((x i).1 * (x i).2) +
      ((orderedPairs m).map fun p =>
        if p.1.1 = i then (tr p).1 else if p.1.2 = i then (tr p).2 else 0).sum,
   fun i => ((orderedPairs m).map fun p => if p.1.1 = i then [(tr p).1] else []).flatten,
   fun i => ((orderedPairs m).map fun p => if p.1.2 = i then [(tr p).2] else []).flatten)

/-- Deterministic extraction of `(ot_c_delta, ot_a_delta)` from one simulated `multiPartyMulSim m I`
invocation composed with `twoPartyMulSim`. -/
private def simSharedMulPure (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (x : Fin m → Bool × Bool) (ans : Fin m → Bool) (r : OrderedPair m → Bool) :
    (Fin m → List Bool) × (Fin m → List Bool) :=
  let x₀ := MultiPartyMul.extendIn I (I.restrict x)
  let y₀ := MultiPartyMul.extendOut I (I.restrict ans)
  let rSim := MultiPartyMul.tildeR (MultiPartyMul.pivotParty I) x₀ y₀ r
  (fun i =>
    ((orderedPairs m).map fun p =>
      if p.1.1 = i then [MultiPartyMul.matrixOfCoins x₀ rSim i p.1.2] else []).flatten,
   fun i =>
    ((orderedPairs m).map fun p =>
      if p.1.2 = i then [MultiPartyMul.matrixOfCoins x₀ rSim i p.1.1] else []).flatten)

/-- Step 2 accumulator `(wires, ot_coins, ot_ans)`. -/
private abbrev Step2Acc (m : ℕ) : Type :=
  (Fin m → List Bool) × (Fin m → List Bool) × (Fin m → List Bool)

/-- Encoding of `Step2Acc m`. -/
private noncomputable def encStep2Acc (m : ℕ) : Step2Acc m ↪ List Bool :=
  encPair (encPi encBits) (encPair (encPi encBits) (encPi encBits))

/-- Append per-party Step 2 deltas `(w_delta, ot_c_delta, ot_a_delta)` to `acc : Step2Acc m`. -/
private def appendStep2Acc (m : ℕ) (acc delta : Step2Acc m) : Step2Acc m :=
  (fun i => acc.1 i ++ delta.1 i,
   fun i => acc.2.1 i ++ delta.2.1 i,
   fun i => acc.2.2 i ++ delta.2.2 i)

private theorem computableTidilyInPolyTime_appendPiBits (m : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : (Fin m → List Bool) × (Fin m → List Bool) => fun i => p.1 i ++ p.2 i)
      (encPair (encPi encBits) (encPi encBits)) (encPi encBits) :=
  pi fun i =>
    bitsAppend
      ((pi_apply encBits i).comp (fst (encPi encBits) (encPi encBits)))
      ((pi_apply encBits i).comp (snd (encPi encBits) (encPi encBits)))

private theorem computableTidilyInPolyTime_appendStep2Acc (m : ℕ) :
    ComputableTidilyInPolyTime (fun p : Step2Acc m × Step2Acc m => appendStep2Acc m p.1 p.2)
      (encPair (encStep2Acc m) (encStep2Acc m)) (encStep2Acc m) := by
  let e := encPi (Index := Fin m) encBits
  let e2 := encPair e e
  let e3 := encStep2Acc m
  have h1 := (computableTidilyInPolyTime_appendPiBits m).comp
    (((fst e e2).comp (fst e3 e3)).prod ((fst e e2).comp (snd e3 e3)))
  have h2 := (computableTidilyInPolyTime_appendPiBits m).comp
    ((((fst e e).comp (snd e e2)).comp (fst e3 e3)).prod
      (((fst e e).comp (snd e e2)).comp (snd e3 e3)))
  have h3 := (computableTidilyInPolyTime_appendPiBits m).comp
    ((((snd e e).comp (snd e e2)).comp (fst e3 e3)).prod
      (((snd e e).comp (snd e e2)).comp (snd e3 e3)))
  exact h1.prod (h2.prod h3)

private theorem length_encStep2Acc_appendStep2Acc_le (m : ℕ) (acc delta : Step2Acc m)
    (hw : ∀ i, (delta.1 i).length ≤ 1)
    (hc : ∀ i, (delta.2.1 i).length ≤ (orderedPairs m).length)
    (ha : ∀ i, (delta.2.2 i).length ≤ (orderedPairs m).length) :
    (encStep2Acc m (appendStep2Acc m acc delta)).length ≤
      (encStep2Acc m acc).length + m * (4 + 6 * (orderedPairs m).length) := by
  have h1 := length_encPi_encBits_le acc.1 (fun i => acc.1 i ++ delta.1 i) 1
    (fun i => by simp [hw i])
  have h2 := length_encPi_encBits_le acc.2.1 (fun i => acc.2.1 i ++ delta.2.1 i)
    (orderedPairs m).length (fun i => by simp [hc i])
  have h3 := length_encPi_encBits_le acc.2.2 (fun i => acc.2.2 i ++ delta.2.2 i)
    (orderedPairs m).length (fun i => by simp [ha i])
  have hr : m * (4 + 6 * (orderedPairs m).length) =
      2 * (m * (2 * 1)) + 2 * (m * (2 * (orderedPairs m).length)) +
        m * (2 * (orderedPairs m).length) := by
    ring
  simp only [encStep2Acc, appendStep2Acc, encPair_apply, List.length_append, length_frame, hr]
  omega

/-- Extract `(op, x)` from `(gate, acc)` for Step 2 gate evaluation. -/
private def extractGateCoreInput (m : ℕ) (st : (Boolean.Op × List ℕ) × Step2Acc m) :
    Boolean.Op × (Fin m → Bool × Bool) :=
  (st.1.1, fun s =>
    ((st.2.1 s).getD (st.1.2.getD 0 0) false,
     (st.2.1 s).getD (st.1.2.getD 1 0) false))

private theorem computableTidilyInPolyTime_extractGateCoreInput (m : ℕ) :
    ComputableTidilyInPolyTime (extractGateCoreInput m)
      (encPair Boolean.encGate (encStep2Acc m))
      (encFinite (Boolean.Op × (Fin m → Bool × Bool))) := by
  let eGate := Boolean.encGate
  let eAcc := encStep2Acc m
  let ePi := encPi (Index := Fin m) encBits
  have hop := (fst Boolean.encOp (encList encNat)).comp (fst eGate eAcc)
  have hwiresList := (snd Boolean.encOp (encList encNat)).comp (fst eGate eAcc)
  have hidx0 := (listGetD (encA := encNat) 0).comp (hwiresList.prod (const 0))
  have hidx1 := (listGetD (encA := encNat) 0).comp (hwiresList.prod (const 1))
  have hx : ComputableTidilyInPolyTime
      (fun st : (Boolean.Op × List ℕ) × Step2Acc m => fun s : Fin m =>
        ((st.2.1 s).getD (st.1.2.getD 0 0) false,
         (st.2.1 s).getD (st.1.2.getD 1 0) false))
      (encPair eGate eAcc) (encPi (encPair encBool encBool)) := by
    refine pi fun s => ?_
    have hws := (pi_apply encBits s).comp ((fst ePi (encPair ePi ePi)).comp (snd eGate eAcc))
    exact (listGetD_binary (encA := encBool) false hws hidx0).prod
      (listGetD_binary (encA := encBool) false hws hidx1)
  exact (of_finite (encA := encPair Boolean.encOp (encPi (encPair encBool encBool)))
    (encB := encFinite (Boolean.Op × (Fin m → Bool × Bool))) id).comp (hop.prod hx)

/-- Format the per-party Step 2 deltas `(w_delta, ot_c_delta, ot_a_delta)` for an `.and`
(`isOr = false`) or `.or` (`isOr = true`) gate. -/
private def finishMulGate (m : ℕ) (isOr : Bool) (x : Fin m → Bool × Bool)
    (res : (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) :
    Step2Acc m :=
  (fun i => [if isOr then (x i).1 + (x i).2 + res.1 i else res.1 i],
   res.2.1, res.2.2)

/-- Finite-input core of one real Step 2 gate evaluation. -/
private noncomputable def realGateCore (m : ℕ) [NeZero m] (p : Boolean.Op × (Fin m → Bool × Bool)) :
    WordOracleComp Unit (Step2Acc m) :=
  match p.1 with
  | .const b =>
    pure (fun i => [GMWCircuit.constShare b i], fun _ => [], fun _ => [])
  | .not =>
    pure (fun i => [(p.2 i).1 + GMWCircuit.constShare true i], fun _ => [], fun _ => [])
  | .and =>
    (fun tr => finishMulGate m false p.2 (realSharedMulPure m p.2 tr)) <$>
      realPairsCalls m p.2 (orderedPairs m)
  | .or =>
    (fun tr => finishMulGate m true p.2 (realSharedMulPure m p.2 tr)) <$>
      realPairsCalls m p.2 (orderedPairs m)

private theorem isOraclePPTOn_realGateCore (m : ℕ) [NeZero m] :
    IsOraclePPTOn (encFinite (Boolean.Op × (Fin m → Bool × Bool))) (encStep2Acc m)
      (realGateCore m) := by
  refine (IsOraclePPTOn.finite_cases
    (tagEncoding := encFinite (Boolean.Op × (Fin m → Bool × Bool)))
    (tag := id) (branch := fun choice _ => realGateCore m choice) id' ?_).congr
    fun _ _ _ _ => rfl
  rintro ⟨op, x⟩
  cases op with
  | const b =>
    exact ((of_finite _).isPPTOn).isOraclePPTOn
  | not =>
    exact ((of_finite _).isPPTOn).isOraclePPTOn
  | and =>
    exact (((isOraclePPTOn_realPairsCalls m (orderedPairs m)).preprocess (const x)).map
      (of_finite (fun tr => finishMulGate m false x (realSharedMulPure m x tr))))
  | or =>
    exact (((isOraclePPTOn_realPairsCalls m (orderedPairs m)).preprocess (const x)).map
      (of_finite (fun tr => finishMulGate m true x (realSharedMulPure m x tr))))

/-- Shared simulated multiplication core: sample additive shares `ans` of `target` and pair coins
`r`, then package `(ans, simSharedMulPure m I x ans r)` with `finish`. -/
private noncomputable def simMulCore (m : ℕ) [NeZero m] {β : Type} (I : Finset (Fin m))
    (target : Bool) (x : Fin m → Bool × Bool)
    (finish : ((Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) → β) :
    ProbComp β := do
  let ans ← ProbComp.sampleAdditiveShares m target
  let r ← ProbComp.uniform (OrderedPair m → Bool)
  return finish (ans, simSharedMulPure m I x ans r)

private theorem isPPTOn_simMulCore (m : ℕ) [NeZero m] {α β : Type} [Finite α]
    (outEnc : β ↪ List Bool) (I : Finset (Fin m))
    (target : Bool) (x : Fin m → Bool × Bool)
    (finish : ((Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) → β) :
    IsPPTOn (encFinite α) outEnc (fun _ => simMulCore m I target x finish) := by
  have hans : IsPPTOn (encFinite α) (encFinite (Fin m → Bool))
      (fun _ => ProbComp.sampleAdditiveShares m target) :=
    (isPPTOn_sampleAdditiveShares m).preprocess (.of_tidy (const target))
  have hot : IsPPTOn (encFinite (Fin m → Bool)) outEnc
      (fun ans => do
        let r ← ProbComp.uniform (OrderedPair m → Bool)
        return finish (ans, simSharedMulPure m I x ans r)) :=
    (isPPTOn_of_finite_uniform (encFinite (Fin m → Bool)) outEnc
      (fun ans r => finish (ans, simSharedMulPure m I x ans r))).congr fun _ => rfl
  exact hans.bind hot

private theorem computableTidilyInPolyTime_appendAcc_post {Item Acc : Type}
    (eItem : Item ↪ List Bool) {eAcc : Acc ↪ List Bool} {append : Acc → Acc → Acc}
    (happend : ComputableTidilyInPolyTime (fun p : Acc × Acc => append p.1 p.2)
      (encPair eAcc eAcc) eAcc) :
    ComputableTidilyInPolyTime
      (fun q : (Item × Acc) × Acc => append q.1.2 q.2)
      (encPair (encPair eItem eAcc) eAcc) eAcc :=
  comp' happend ((comp' (snd eItem eAcc) (fst (encPair eItem eAcc) eAcc)).prod
    (snd (encPair eItem eAcc) eAcc))

/-- Finite-input core of one simulated Step 2 gate evaluation. -/
private noncomputable def simGateCore (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (p : Boolean.Op × (Fin m → Bool × Bool)) :
    ProbComp (Step2Acc m) :=
  match p.1 with
  | .const b =>
    pure (fun i => [GMWCircuit.constShare b i], fun _ => [], fun _ => [])
  | .not =>
    pure (fun i => [(p.2 i).1 + GMWCircuit.constShare true i], fun _ => [], fun _ => [])
  | .and =>
    simMulCore m I ((∑ i : Fin m, (p.2 i).1) * (∑ i : Fin m, (p.2 i).2)) p.2
      (finishMulGate m false p.2)
  | .or =>
    simMulCore m I ((∑ i : Fin m, (p.2 i).1) * (∑ i : Fin m, (p.2 i).2)) p.2
      (finishMulGate m true p.2)

private theorem isPPTOn_simGateCore (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    IsPPTOn (encFinite (Boolean.Op × (Fin m → Bool × Bool))) (encStep2Acc m)
      (simGateCore m I) := by
  refine (IsPPTOn.finite_cases
    (tagEncoding := encFinite (Boolean.Op × (Fin m → Bool × Bool)))
    (tag := id) (branch := fun choice _ => simGateCore m I choice)
    ComputableInPolyTime.id' ?_).congr
    fun _ => rfl
  rintro ⟨op, x⟩
  cases op with
  | const b | not => exact (of_finite _).isPPTOn
  | and => exact isPPTOn_simMulCore m (encStep2Acc m) I _ x (finishMulGate m false x)
  | or => exact isPPTOn_simMulCore m (encStep2Acc m) I _ x (finishMulGate m true x)

/-- Single Step 2 gate transition in `realRunWord`. -/
private noncomputable def realGateStep (m : ℕ) [NeZero m] (gate : Boolean.Op × List ℕ)
    (acc : Step2Acc m) :
    WordOracleComp Unit (Step2Acc m) :=
  appendStep2Acc m acc <$> realGateCore m (extractGateCoreInput m (gate, acc))

private theorem isOraclePPTOn_realGateStep (m : ℕ) [NeZero m] :
    IsOraclePPTOn (encPair Boolean.encGate (encStep2Acc m)) (encStep2Acc m)
      (fun p => realGateStep m p.1 p.2) :=
  ((isOraclePPTOn_realGateCore m).preprocess
    (computableTidilyInPolyTime_extractGateCoreInput m)).map_with
    (f := fun (p : (Boolean.Op × List ℕ) × Step2Acc m) delta => appendStep2Acc m p.2 delta)
    (computableTidilyInPolyTime_appendAcc_post Boolean.encGate
      (computableTidilyInPolyTime_appendStep2Acc m))

private theorem realGateStep_growth (m : ℕ) [NeZero m]
    (gate : Boolean.Op × List ℕ) (acc next : Step2Acc m)
    (hnext : next ∈ OracleComp.support (realGateStep m gate acc)) :
    (encStep2Acc m next).length ≤
      (encStep2Acc m acc).length + m * (4 + 6 * (orderedPairs m).length) := by
  obtain ⟨delta, hdelta, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  rcases hg : extractGateCoreInput m (gate, acc) with ⟨op, x⟩
  rw [hg] at hdelta
  cases op with
  | const b | not =>
    obtain rfl := OracleComp.eq_of_mem_supportWith_pure hdelta
    exact length_encStep2Acc_appendStep2Acc_le m acc _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
  | and | or =>
    simp only [realGateCore] at hdelta
    obtain ⟨tr, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hdelta
    exact length_encStep2Acc_appendStep2Acc_le m acc _
      (fun _ => by simp [finishMulGate])
      (fun _ => length_flatten_ite_singleton_le _ _ _)
      (fun _ => length_flatten_ite_singleton_le _ _ _)

/-- Single Step 2 gate transition in `simRunWord`. -/
private noncomputable def simGateStep (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (gate : Boolean.Op × List ℕ) (acc : Step2Acc m) :
    ProbComp (Step2Acc m) :=
  appendStep2Acc m acc <$> simGateCore m I (extractGateCoreInput m (gate, acc))

private theorem isPPTOn_simGateStep (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    IsPPTOn (encPair Boolean.encGate (encStep2Acc m)) (encStep2Acc m)
      (fun p => simGateStep m I p.1 p.2) :=
  ((isPPTOn_simGateCore m I).preprocess
    (.of_tidy (computableTidilyInPolyTime_extractGateCoreInput m))).map_with
    (f := fun (p : (Boolean.Op × List ℕ) × Step2Acc m) delta => appendStep2Acc m p.2 delta)
    (.of_tidy (computableTidilyInPolyTime_appendAcc_post Boolean.encGate
      (computableTidilyInPolyTime_appendStep2Acc m)))

private theorem simGateStep_growth (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (gate : Boolean.Op × List ℕ) (acc next : Step2Acc m)
    (hnext : next ∈ (ProbComp.eval (simGateStep m I gate acc)).support) :
    (encStep2Acc m next).length ≤
      (encStep2Acc m acc).length + m * (4 + 6 * (orderedPairs m).length) := by
  simp only [simGateStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
  obtain ⟨delta, hdelta, rfl⟩ := hnext
  rcases hg : extractGateCoreInput m (gate, acc) with ⟨op, x⟩
  rw [hg] at hdelta
  cases op with
  | const b | not =>
    simp only [simGateCore, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hdelta
    subst hdelta
    exact length_encStep2Acc_appendStep2Acc_le m acc _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
  | and | or =>
    simp only [simGateCore, simMulCore, ProbComp.eval_bind, ProbComp.eval_map,
      bind_pure_comp, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hdelta
    obtain ⟨ans, _, r, _, rfl⟩ := hdelta
    exact length_encStep2Acc_appendStep2Acc_le m acc _
      (fun _ => by simp [finishMulGate])
      (fun _ => length_flatten_ite_singleton_le _ _ _)
      (fun _ => length_flatten_ite_singleton_le _ _ _)

/-- Step 3 item `(r_party, a_shares, y_bit)` for output coordinate `(r_party, j)`. -/
private abbrev OutItem (m : ℕ) : Type :=
  Fin m × (Fin m → Bool) × Bool

/-- Step 3 accumulator `(ot_coins, ot_ans, out_msgs, y_out)`. -/
private abbrev Step3Acc (m : ℕ) : Type :=
  (Fin m → List Bool) × (Fin m → List Bool) × (Fin m → List Bool) × (Fin m → List Bool)

/-- Encoding of `Step3Acc m`. -/
private noncomputable def encStep3Acc (m : ℕ) : Step3Acc m ↪ List Bool :=
  encPair (encPi encBits) (encPair (encPi encBits) (encPair (encPi encBits) (encPi encBits)))

/-- Append per-party Step 3 deltas `(ot_c_delta, ot_a_delta, msg_delta, y_delta)` to `acc`. -/
private def appendStep3Acc (m : ℕ) (acc delta : Step3Acc m) : Step3Acc m :=
  (fun i => acc.1 i ++ delta.1 i,
   fun i => acc.2.1 i ++ delta.2.1 i,
   fun i => acc.2.2.1 i ++ delta.2.2.1 i,
   fun i => acc.2.2.2 i ++ delta.2.2.2 i)

private theorem computableTidilyInPolyTime_appendStep3Acc (m : ℕ) :
    ComputableTidilyInPolyTime (fun p : Step3Acc m × Step3Acc m => appendStep3Acc m p.1 p.2)
      (encPair (encStep3Acc m) (encStep3Acc m)) (encStep3Acc m) := by
  let e := encPi (Index := Fin m) encBits
  let e2 := encStep2Acc m
  let e3 := encStep3Acc m
  have h1 := (computableTidilyInPolyTime_appendPiBits m).comp
    (((fst e e2).comp (fst e3 e3)).prod ((fst e e2).comp (snd e3 e3)))
  have h234 := (computableTidilyInPolyTime_appendStep2Acc m).comp
    (((snd e e2).comp (fst e3 e3)).prod ((snd e e2).comp (snd e3 e3)))
  exact h1.prod h234

private theorem length_encStep3Acc_appendStep3Acc_le (m : ℕ) (acc delta : Step3Acc m)
    (hc : ∀ i, (delta.1 i).length ≤ (orderedPairs m).length)
    (ha : ∀ i, (delta.2.1 i).length ≤ (orderedPairs m).length)
    (hm : ∀ i, (delta.2.2.1 i).length ≤ m)
    (hy : ∀ i, (delta.2.2.2 i).length ≤ 1) :
    (encStep3Acc m (appendStep3Acc m acc delta)).length ≤
      (encStep3Acc m acc).length + m * (2 + 4 * m + 8 * (orderedPairs m).length) := by
  have h1 := length_encPi_encBits_le acc.1 (fun i => acc.1 i ++ delta.1 i)
    (orderedPairs m).length (fun i => by simp [hc i])
  have h2 := length_encPi_encBits_le acc.2.1 (fun i => acc.2.1 i ++ delta.2.1 i)
    (orderedPairs m).length (fun i => by simp [ha i])
  have h3 := length_encPi_encBits_le acc.2.2.1 (fun i => acc.2.2.1 i ++ delta.2.2.1 i)
    m (fun i => by simp [hm i])
  have h4 := length_encPi_encBits_le acc.2.2.2 (fun i => acc.2.2.2 i ++ delta.2.2.2 i)
    1 (fun i => by simp [hy i])
  have hr : m * (2 + 4 * m + 8 * (orderedPairs m).length) =
      2 * (m * (2 * (orderedPairs m).length)) +
        2 * (m * (2 * (orderedPairs m).length)) +
        2 * (m * (2 * m)) +
        m * (2 * 1) := by
    ring
  simp only [encStep3Acc, appendStep3Acc, encPair_apply, List.length_append, length_frame, hr]
  omega

/-- Build the list of `m * k` Step 3 items `(r_party, a_shares, y_bit)` from the designated output
wire indices `outputs : List ℕ`, final wire lists `wires : Fin m → List Bool`, and target output
bits `y_bits : Fin m → List Bool`. -/
private def buildOutItems (m k : ℕ) (I : Finset (Fin m))
    (outputs : List ℕ) (wires y_bits : Fin m → List Bool) :
    List (OutItem m) :=
  (List.finRange m).flatMap fun r =>
    (List.range k).map fun j =>
      let wIdx := outputs.getD (r.val * k + j) 0
      (r,
       fun s => (wires s).getD wIdx false,
       if r ∈ I then (y_bits r).getD j false else false)

private theorem computableTidilyInPolyTime_buildOutItems {α : Type} {input : α ↪ List Bool}
    (m : ℕ) (I : Finset (Fin m)) {k : α → ℕ}
    {outputs : α → List ℕ} {wires y_bits : α → Fin m → List Bool}
    (hk : ComputableTidilyInPolyTime k input encUnary)
    (houtputs : ComputableTidilyInPolyTime outputs input (encList encNat))
    (hwires : ComputableTidilyInPolyTime wires input (encPi encBits))
    (hy : ComputableTidilyInPolyTime y_bits input (encPi encBits)) :
    ComputableTidilyInPolyTime
      (fun a => buildOutItems m (k a) I (outputs a) (wires a) (y_bits a))
      input (encList (encFinite (OutItem m))) := by
  refine flatMapConst (List.finRange m) fun r _ => ?_
  have hkBin := unary_to_binary.comp (hk.comp (fst input encUnary))
  have hjBin := unary_to_binary.comp (snd input encUnary)
  have hidx := binary_add' (binary_mul' (const r.val) hkBin) hjBin
  have hwIdx := listGetD_binary (encA := encNat) 0 (houtputs.comp (fst input encUnary)) hidx
  have ha_shares : ComputableTidilyInPolyTime
      (fun p : α × ℕ => fun s : Fin m =>
        ((wires p.1) s).getD ((outputs p.1).getD (r.val * k p.1 + p.2) 0) false)
      (encPair input encUnary) (encPi encBool) := by
    refine pi fun s => ?_
    exact listGetD_binary (encA := encBool) false
      (((pi_apply encBits s).comp hwires).comp (fst input encUnary)) hwIdx
  have hy_bit : ComputableTidilyInPolyTime
      (fun p : α × ℕ => if r ∈ I then (y_bits p.1 r).getD p.2 false else false)
      (encPair input encUnary) encBool := by
    by_cases hr : r ∈ I
    · simpa only [hr, ↓reduceIte, Function.comp_def] using
        bitsGetDWithInput (((pi_apply encBits r).comp hy).comp (fst input encUnary))
          (snd input encUnary) false
    · simpa only [hr, ↓reduceIte] using const false
  have hpack : ComputableTidilyInPolyTime
      (fun q : (Fin m → Bool) × Bool => (r, q.1, q.2))
      (encPair (encPi encBool) encBool) (encFinite (OutItem m)) :=
    of_finite _
  have hbody := hpack.comp (ha_shares.prod hy_bit)
  exact mapWithInput (range.comp hk) hbody

/-- Format the per-party Step 3 deltas `(ot_c_delta, ot_a_delta, msg_delta, y_delta)` for recipient
`r_party : Fin m`. -/
private def finishOutStep (m : ℕ) (r_party : Fin m)
    (res : (Fin m → Bool) × (Fin m → List Bool) × (Fin m → List Bool)) :
    Step3Acc m :=
  (res.2.1,
   res.2.2,
   fun i => if i = r_party then List.ofFn res.1 else [],
   fun i => if i = r_party then [∑ s : Fin m, res.1 s] else [])

/-- Finite-input core of one real Step 3 output-coordinate refresh and reconstruction. -/
private noncomputable def realOutCore (m : ℕ) [NeZero m] (item : OutItem m) :
    WordOracleComp Unit (Step3Acc m) :=
  (fun tr =>
    finishOutStep m item.1
      (realSharedMulPure m (fun s => (item.2.1 s, GMWCircuit.constShare true s)) tr)) <$>
    realPairsCalls m (fun s => (item.2.1 s, GMWCircuit.constShare true s)) (orderedPairs m)

private theorem isOraclePPTOn_realOutCore (m : ℕ) [NeZero m] :
    IsOraclePPTOn (encFinite (OutItem m)) (encStep3Acc m) (realOutCore m) := by
  refine (IsOraclePPTOn.finite_cases
    (tagEncoding := encFinite (OutItem m))
    (tag := id) (branch := fun item _ => realOutCore m item) id' ?_).congr
    fun _ _ _ _ => rfl
  intro item
  exact (((isOraclePPTOn_realPairsCalls m (orderedPairs m)).preprocess
    (const (fun s => (item.2.1 s, GMWCircuit.constShare true s)))).map
    (of_finite (fun tr =>
      finishOutStep m item.1
        (realSharedMulPure m (fun s => (item.2.1 s, GMWCircuit.constShare true s)) tr))))

/-- Finite-input core of one simulated Step 3 output-coordinate refresh and reconstruction. -/
private noncomputable def simOutCore (m : ℕ) [NeZero m] (I : Finset (Fin m)) (item : OutItem m) :
    ProbComp (Step3Acc m) :=
  simMulCore m I item.2.2 (fun s => (item.2.1 s, GMWCircuit.constShare true s))
    (finishOutStep m item.1)

private theorem isPPTOn_simOutCore (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    IsPPTOn (encFinite (OutItem m)) (encStep3Acc m) (simOutCore m I) := by
  refine (IsPPTOn.finite_cases
    (tagEncoding := encFinite (OutItem m))
    (tag := id) (branch := fun item _ => simOutCore m I item)
    ComputableInPolyTime.id' ?_).congr
    fun _ => rfl
  intro item
  exact isPPTOn_simMulCore m (encStep3Acc m) I item.2.2 _ (finishOutStep m item.1)

/-- Single Step 3 output-coordinate transition in `realRunWord`. -/
private noncomputable def realOutStep (m : ℕ) [NeZero m] (item : OutItem m) (acc : Step3Acc m) :
    WordOracleComp Unit (Step3Acc m) :=
  appendStep3Acc m acc <$> realOutCore m item

private theorem isOraclePPTOn_realOutStep (m : ℕ) [NeZero m] :
    IsOraclePPTOn (encPair (encFinite (OutItem m)) (encStep3Acc m)) (encStep3Acc m)
      (fun p => realOutStep m p.1 p.2) :=
  ((isOraclePPTOn_realOutCore m).preprocess (fst (encFinite (OutItem m)) (encStep3Acc m))).map_with
    (f := fun (p : OutItem m × Step3Acc m) delta => appendStep3Acc m p.2 delta)
    (computableTidilyInPolyTime_appendAcc_post (encFinite (OutItem m))
      (computableTidilyInPolyTime_appendStep3Acc m))

private theorem realOutStep_growth (m : ℕ) [NeZero m]
    (item : OutItem m) (acc next : Step3Acc m)
    (hnext : next ∈ OracleComp.support (realOutStep m item acc)) :
    (encStep3Acc m next).length ≤
      (encStep3Acc m acc).length + m * (2 + 4 * m + 8 * (orderedPairs m).length) := by
  obtain ⟨delta, hdelta, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  simp only [realOutCore] at hdelta
  obtain ⟨tr, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hdelta
  exact length_encStep3Acc_appendStep3Acc_le m acc _
    (fun _ => length_flatten_ite_singleton_le _ _ _)
    (fun _ => length_flatten_ite_singleton_le _ _ _)
    (fun _ => by dsimp only [finishOutStep]; split_ifs <;> simp)
    (fun _ => by dsimp only [finishOutStep]; split_ifs <;> simp)

/-- Single Step 3 output-coordinate transition in `simRunWord`. -/
private noncomputable def simOutStep (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (item : OutItem m) (acc : Step3Acc m) :
    ProbComp (Step3Acc m) :=
  appendStep3Acc m acc <$> simOutCore m I item

private theorem isPPTOn_simOutStep (m : ℕ) [NeZero m] (I : Finset (Fin m)) :
    IsPPTOn (encPair (encFinite (OutItem m)) (encStep3Acc m)) (encStep3Acc m)
      (fun p => simOutStep m I p.1 p.2) :=
  ((isPPTOn_simOutCore m I).preprocess
    (.of_tidy (fst (encFinite (OutItem m)) (encStep3Acc m)))).map_with
    (f := fun (p : OutItem m × Step3Acc m) delta => appendStep3Acc m p.2 delta)
    (.of_tidy (computableTidilyInPolyTime_appendAcc_post (encFinite (OutItem m))
      (computableTidilyInPolyTime_appendStep3Acc m)))

private theorem simOutStep_growth (m : ℕ) [NeZero m] (I : Finset (Fin m))
    (item : OutItem m) (acc next : Step3Acc m)
    (hnext : next ∈ (ProbComp.eval (simOutStep m I item acc)).support) :
    (encStep3Acc m next).length ≤
      (encStep3Acc m acc).length + m * (2 + 4 * m + 8 * (orderedPairs m).length) := by
  simp only [simOutStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
  obtain ⟨delta, hdelta, rfl⟩ := hnext
  simp only [simOutCore, simMulCore, ProbComp.eval_bind, ProbComp.eval_map,
    bind_pure_comp, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hdelta
  obtain ⟨ans, _, r, _, rfl⟩ := hdelta
  exact length_encStep3Acc_appendStep3Acc_le m acc _
    (fun _ => length_flatten_ite_singleton_le _ _ _)
    (fun _ => length_flatten_ite_singleton_le _ _ _)
    (fun _ => by dsimp only [finishOutStep]; split_ifs <;> simp)
    (fun _ => by dsimp only [finishOutStep]; split_ifs <;> simp)

/-- Party `i`'s view word `gmwViewWord` from the seven per-party component words. -/
private def packPartyViewWord {m : ℕ}
    (x_bits r_bits c1_bits ot_coins in_shares ot_ans out_msgs : Fin m → List Bool)
    (i : Fin m) : List Bool :=
  gmwViewWord (x_bits i) (r_bits i) (c1_bits i) (ot_coins i) (in_shares i) (ot_ans i) (out_msgs i)

private theorem computableTidilyInPolyTime_gmwViewWord {α : Type} {input : α ↪ List Bool}
    {x r c1 otc ins ota out : α → List Bool}
    (hx : ComputableTidilyInPolyTime x input encBits)
    (hr : ComputableTidilyInPolyTime r input encBits)
    (hc1 : ComputableTidilyInPolyTime c1 input encBits)
    (hotc : ComputableTidilyInPolyTime otc input encBits)
    (hins : ComputableTidilyInPolyTime ins input encBits)
    (hota : ComputableTidilyInPolyTime ota input encBits)
    (hout : ComputableTidilyInPolyTime out input encBits) :
    ComputableTidilyInPolyTime
      (fun a => gmwViewWord (x a) (r a) (c1 a) (otc a) (ins a) (ota a) (out a)) input encBits :=
  (((hx.prod hr).prod (hc1.prod hotc)).prod (hins.prod (hota.prod hout))).encoded

/-- Assemble the final `List Bool` output of `Protocol.runEncoded` from all 8 `Fin m → List Bool`
components `(x_bits, r_bits, c1_bits, in_shares)` and
`acc3 = (ot_coins, ot_ans, out_msgs, y_out)`. -/
private def packRealOutput (m : ℕ)
    (x_bits r_bits c1_bits in_shares : Fin m → List Bool)
    (acc3 : Step3Acc m) : List Bool :=
  encPair (encList encBits) (encList encBits)
    ((List.finRange m).map
       (packPartyViewWord x_bits r_bits c1_bits acc3.1 in_shares acc3.2.1 acc3.2.2.1),
     (List.finRange m).map acc3.2.2.2)

/-- Assemble the final `List Bool` output of `encodeCoalitionView` from `(x_bits, r_bits, c1_bits,
in_shares)` and `acc3 = (ot_coins, ot_ans, out_msgs, y_out)`. -/
private def packSimOutput (m : ℕ) (I : Finset (Fin m))
    (x_bits r_bits c1_bits in_shares : Fin m → List Bool)
    (acc3 : Step3Acc m) : List Bool :=
  encList encBits
    ((List.finRange m).map fun i =>
      if i ∈ I then
        packPartyViewWord x_bits r_bits c1_bits acc3.1 in_shares acc3.2.1 acc3.2.2.1 i
      else [])

private theorem computableTidilyInPolyTime_packPartyViewWord {α : Type} {input : α ↪ List Bool}
    {m : ℕ} {x_bits r_bits c1_bits in_shares : α → Fin m → List Bool} {acc3 : α → Step3Acc m}
    (hx : ComputableTidilyInPolyTime x_bits input (encPi encBits))
    (hr : ComputableTidilyInPolyTime r_bits input (encPi encBits))
    (hc1 : ComputableTidilyInPolyTime c1_bits input (encPi encBits))
    (hin : ComputableTidilyInPolyTime in_shares input (encPi encBits))
    (hacc3 : ComputableTidilyInPolyTime acc3 input (encStep3Acc m))
    (i : Fin m) :
    ComputableTidilyInPolyTime
      (fun a => packPartyViewWord (x_bits a) (r_bits a) (c1_bits a) (acc3 a).1
        (in_shares a) (acc3 a).2.1 (acc3 a).2.2.1 i)
      input encBits := by
  let ePi := encPi (Index := Fin m) encBits
  have hot_c := comp' (fst ePi (encPair ePi (encPair ePi ePi))) hacc3
  have hrest1 := comp' (snd ePi (encPair ePi (encPair ePi ePi))) hacc3
  have hot_a := comp' (fst ePi (encPair ePi ePi)) hrest1
  have hout_m := comp' (fst ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hrest1)
  exact computableTidilyInPolyTime_gmwViewWord (comp' (pi_apply encBits i) hx)
    (comp' (pi_apply encBits i) hr) (comp' (pi_apply encBits i) hc1)
    (comp' (pi_apply encBits i) hot_c) (comp' (pi_apply encBits i) hin)
    (comp' (pi_apply encBits i) hot_a) (comp' (pi_apply encBits i) hout_m)

private theorem computableTidilyInPolyTime_packRealOutput {α : Type} {input : α ↪ List Bool}
    {m : ℕ} {x_bits r_bits c1_bits in_shares : α → Fin m → List Bool}
    {acc3 : α → Step3Acc m}
    (hx : ComputableTidilyInPolyTime x_bits input (encPi encBits))
    (hr : ComputableTidilyInPolyTime r_bits input (encPi encBits))
    (hc1 : ComputableTidilyInPolyTime c1_bits input (encPi encBits))
    (hin : ComputableTidilyInPolyTime in_shares input (encPi encBits))
    (hacc3 : ComputableTidilyInPolyTime acc3 input (encStep3Acc m)) :
    ComputableTidilyInPolyTime
      (fun a => packRealOutput m (x_bits a) (r_bits a) (c1_bits a) (in_shares a) (acc3 a))
      input encBits := by
  let ePi := encPi (Index := Fin m) encBits
  have hy_out := comp' (snd ePi ePi) (comp' (snd ePi (encPair ePi ePi))
    (comp' (snd ePi (encPair ePi (encPair ePi ePi))) hacc3))
  have hviews := ofFn fun i =>
    computableTidilyInPolyTime_packPartyViewWord hx hr hc1 hin hacc3 i
  have houts := ofFn fun i => comp' (pi_apply encBits i) hy_out
  simpa only [packRealOutput, List.ofFn_eq_map] using (hviews.prod houts).encoded

private theorem computableTidilyInPolyTime_packSimOutput {α : Type} {input : α ↪ List Bool}
    {m : ℕ} (I : Finset (Fin m))
    {x_bits r_bits c1_bits in_shares : α → Fin m → List Bool}
    {acc3 : α → Step3Acc m}
    (hx : ComputableTidilyInPolyTime x_bits input (encPi encBits))
    (hr : ComputableTidilyInPolyTime r_bits input (encPi encBits))
    (hc1 : ComputableTidilyInPolyTime c1_bits input (encPi encBits))
    (hin : ComputableTidilyInPolyTime in_shares input (encPi encBits))
    (hacc3 : ComputableTidilyInPolyTime acc3 input (encStep3Acc m)) :
    ComputableTidilyInPolyTime
      (fun a => packSimOutput m I (x_bits a) (r_bits a) (c1_bits a) (in_shares a) (acc3 a))
      input encBits := by
  have hviewsI : ComputableTidilyInPolyTime
      (fun a => List.ofFn fun i : Fin m =>
        if i ∈ I then
          packPartyViewWord (x_bits a) (r_bits a) (c1_bits a) (acc3 a).1
            (in_shares a) (acc3 a).2.1 (acc3 a).2.2.1 i
        else [])
      input (encList encBits) := by
    refine ofFn fun i => ?_
    by_cases hi : i ∈ I
    · simpa only [hi, ↓reduceIte] using
        computableTidilyInPolyTime_packPartyViewWord hx hr hc1 hin hacc3 i
    · simpa only [hi, ↓reduceIte] using const (encIn := input) (encMid := encBits) ([] : List Bool)
  simpa only [packSimOutput, List.ofFn_eq_map] using hviewsI.encoded

private noncomputable def sampleTwoPiBits (m : ℕ) (w1 w2 : Fin m → ℕ) :
    ProbComp ((Fin m → List Bool) × (Fin m → List Bool)) := do
  let r ← OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (w1 i))
  (fun c => (r, c)) <$> OracleComp.pi (fun i : Fin m => Cslib.BitString.sampleList (w2 i))

private theorem isPPTOn_sampleTwoPiBits {α : Type} {input : α ↪ List Bool}
    {m : ℕ} {w1 w2 : α → Fin m → ℕ}
    (hw1 : ∀ i : Fin m, ComputableTidilyInPolyTime (fun a => w1 a i) input encUnary)
    (hw2 : ∀ i : Fin m, ComputableTidilyInPolyTime (fun a => w2 a i) input encUnary) :
    IsPPTOn input (encPair (encPi encBits) (encPi encBits))
      (fun a => sampleTwoPiBits m (w1 a) (w2 a)) := by
  let ePi := encPi (Index := Fin m) encBits
  have h1 := isPPTOn_pi_sampleList m hw1
  have h2 := isPPTOn_pi_sampleList (input := encPair input ePi) m
    (fun i => comp' (hw2 i) (fst input ePi))
  have h2_pair := h2.pair (snd input ePi)
  simpa only [sampleTwoPiBits, bind_map_left] using h1.keep_input.bind h2_pair

private theorem computableTidilyInPolyTime_familyRunInput_bits
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n encA encUnary) :
    ComputableTidilyInPolyTime
      (fun (inp : FamilyRunInput α m n) (i : Fin m) => List.ofFn (inp.inputs i))
      (encFamilyRunInput encA m n) (encPi encBits) := by
  have ha := (encFamilyRunInput_index_polyTime encA m n ComputableInPolyTime.id').tidy
  have hword := (encFamilyRunInput_inputs_polyTime encA m n ComputableInPolyTime.id').tidy
  refine pi fun i => ?_
  convert bitsRowWithInput (comp' hn ha) (const i.val) hword using 1
  funext inp
  rw [Cslib.BitString.listRow_eq_ofFn (n inp.index) i,
    Cslib.BitString.ofList_ofFn, Cslib.BitString.block_blocksEquiv_symm]

private theorem listRow_extendCoalitionBits {m len : ℕ} (I : Finset (Fin m))
    (vI : (i : I) → BitString len) (i : Fin m) :
    Cslib.BitString.listRow len i.val (extendCoalitionBits I vI) =
      if hi : i ∈ I then List.ofFn (vI ⟨i, hi⟩) else List.replicate len false := by
  rw [extendCoalitionBits, Cslib.BitString.listRow_eq_ofFn len i,
    Cslib.BitString.ofList_ofFn, Cslib.BitString.block_blocksEquiv_symm]
  dsimp only [GMWCircuit.extendByZero]
  split_ifs with hi
  · rfl
  · exact List.ofFn_const len false

private theorem computableTidilyInPolyTime_familySimInput_bits
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n k len : α → ℕ} {I : Finset (Fin m)}
    (v : (inp : FamilySimInput α m n k I) → (i : I) → BitString (len inp.index))
    (hlen : ComputableTidilyInPolyTime len encA encUnary)
    (hword : ComputableTidilyInPolyTime (fun inp => extendCoalitionBits I (v inp))
      (encFamilySimInput encA m n k I) encBits) :
    ComputableTidilyInPolyTime
      (fun (inp : FamilySimInput α m n k I) (i : Fin m) =>
        if hi : i ∈ I then List.ofFn (v inp ⟨i, hi⟩) else List.replicate (len inp.index) false)
      (encFamilySimInput encA m n k I) (encPi encBits) := by
  have ha := (encFamilySimInput_index_polyTime encA m n k I ComputableInPolyTime.id').tidy
  refine pi fun i => ?_
  convert bitsRowWithInput (comp' hlen ha) (const i.val) hword using 1
  funext inp
  exact (listRow_extendCoalitionBits I (v inp) i).symm

private theorem computableTidilyInPolyTime_familySimInput_x_bits
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n k : α → ℕ} {I : Finset (Fin m)}
    (hn : ComputableTidilyInPolyTime n encA encUnary) :
    ComputableTidilyInPolyTime
      (fun (inp : FamilySimInput α m n k I) (i : Fin m) =>
        if hi : i ∈ I then List.ofFn (inp.inputs ⟨i, hi⟩) else List.replicate (n inp.index) false)
      (encFamilySimInput encA m n k I) (encPi encBits) :=
  computableTidilyInPolyTime_familySimInput_bits (fun inp => inp.inputs) hn
    (encFamilySimInput_inputs_polyTime encA m n k I ComputableInPolyTime.id').tidy

private theorem computableTidilyInPolyTime_familySimInput_y_bits
    {α : Type} {encA : α ↪ List Bool} {m : ℕ} {n k : α → ℕ} {I : Finset (Fin m)}
    (hk : ComputableTidilyInPolyTime k encA encUnary) :
    ComputableTidilyInPolyTime
      (fun (inp : FamilySimInput α m n k I) (i : Fin m) =>
        if hi : i ∈ I then List.ofFn (inp.outputs ⟨i, hi⟩) else List.replicate (k inp.index) false)
      (encFamilySimInput encA m n k I) (encPi encBits) :=
  computableTidilyInPolyTime_familySimInput_bits (fun inp => inp.outputs) hk
    (encFamilySimInput_outputs_polyTime encA m n k I ComputableInPolyTime.id').tidy

/-- Word-level runner for `Protocol.runEncoded` applied to `gmwOT14RandomizedProtocol` on a
polynomial-time circuit code family `D : α → List (Boolean.Op × List ℕ) × List ℕ`. -/
private noncomputable def realRunWord {α : Type} (m : ℕ) [NeZero m] (coins n k : α → ℕ)
    (D : α → List (Boolean.Op × List ℕ) × List ℕ)
    (inp : FamilyRunInput α m n) : WordOracleComp Unit (List Bool) := do
  let a := inp.index
  let x_bits : Fin m → List Bool := fun i => List.ofFn (inp.inputs i)
  let rc ← ProbOracleComp.sample
    (sampleTwoPiBits m (fun _ => coins a) (fun _ => (n a + coins a) * (m - 1)))
  let in_shares := step1Wires m (n a + coins a) x_bits rc.1 rc.2
  let init2 : Step2Acc m := (in_shares, fun _ => [], fun _ => [])
  let acc2 ← (D a).1.foldlM (flip (realGateStep m)) init2
  let outItems := buildOutItems m (k a) Finset.univ (D a).2 acc2.1 (fun _ => [])
  let init3 : Step3Acc m := (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
  let acc3 ← List.foldlM (flip (realOutStep m)) init3 outItems
  return packRealOutput m x_bits rc.1 rc.2 in_shares acc3

/-- Word-level simulator for `gmwOT14RandomizedSim` on a polynomial-time circuit code family
`D : α → List (Boolean.Op × List ℕ) × List ℕ`. -/
private noncomputable def simRunWord {α : Type} (m : ℕ) [NeZero m] (coins n k : α → ℕ)
    (D : α → List (Boolean.Op × List ℕ) × List ℕ)
    (I : Finset (Fin m)) (inp : FamilySimInput α m n k I) : ProbComp (List Bool) := do
  let a := inp.index
  let x_bits : Fin m → List Bool := fun i =>
    if hi : i ∈ I then List.ofFn (inp.inputs ⟨i, hi⟩) else List.replicate (n a) false
  let y_bits : Fin m → List Bool := fun i =>
    if hi : i ∈ I then List.ofFn (inp.outputs ⟨i, hi⟩) else List.replicate (k a) false
  let rc ← sampleTwoPiBits m (fun i => if i ∈ I then coins a else 0)
    (fun _ => (n a + coins a) * (m - 1))
  let in_shares := step1Wires m (n a + coins a) x_bits rc.1 rc.2
  let init2 : Step2Acc m := (in_shares, fun _ => [], fun _ => [])
  let acc2 ← (D a).1.foldlM (flip (simGateStep m I)) init2
  let outItems := buildOutItems m (k a) I (D a).2 acc2.1 y_bits
  let init3 : Step3Acc m := (acc2.2.1, acc2.2.2, fun _ => [], fun _ => [])
  let acc3 ← List.foldlM (flip (simOutStep m I)) init3 outItems
  return packSimOutput m I x_bits rc.1 rc.2 in_shares acc3

private theorem isOraclePPTOn_realRunWord {α : Type} {encA : α ↪ List Bool}
    (m : ℕ) [NeZero m] {coins n k : α → ℕ}
    {D : α → List (Boolean.Op × List ℕ) × List ℕ}
    (hcoins : ComputableTidilyInPolyTime coins encA encUnary)
    (hn : ComputableTidilyInPolyTime n encA encUnary)
    (hk : ComputableTidilyInPolyTime k encA encUnary)
    (hD : ComputableTidilyInPolyTime D encA Boolean.encCode) :
    IsOraclePPTOn (Operation := Unit) (encFamilyRunInput encA m n) encBits
      (realRunWord m coins n k D) := by
  let e0 := encFamilyRunInput encA m n
  let ePi := encPi (Index := Fin m) encBits
  let eRC := encPair ePi ePi
  let e1 := encPair e0 eRC
  let e2 := encPair e1 (encStep2Acc m)
  let e3 := encPair e2 (encStep3Acc m)
  have ha0 := (encFamilyRunInput_index_polyTime encA m n ComputableInPolyTime.id').tidy
  have hx0 := computableTidilyInPolyTime_familyRunInput_bits (encA := encA) (m := m) hn
  have hcoins0 := comp' hcoins ha0
  have hn0 := comp' hn ha0
  have hnc0 := comp' unary_add (hn0.prod hcoins0)
  have hw2_0 := comp' unary_mul (hnc0.prod (const (m - 1)))
  have hstage1 := ((isPPTOn_sampleTwoPiBits
    (fun _ : Fin m => hcoins0)
    (fun _ : Fin m => hw2_0)).isOraclePPTOn (Operation := Unit)).keep_input
  have hs1_inp := fst e0 eRC
  have hs1_rc := snd e0 eRC
  have ha1 := comp' ha0 hs1_inp
  have hx1 := comp' hx0 hs1_inp
  have hr1 := comp' (fst ePi ePi) hs1_rc
  have hc1 := comp' (snd ePi ePi) hs1_rc
  have hnc1 := comp' hnc0 hs1_inp
  have hin1 := computableTidilyInPolyTime_step1Wires m hnc1 hx1 hr1 hc1
  have hempty1 : ComputableTidilyInPolyTime
      (fun _ : FamilyRunInput α m n × ((Fin m → List Bool) × (Fin m → List Bool)) =>
        (fun _ : Fin m => ([] : List Bool))) e1 ePi :=
    pi fun _ => const []
  have hinit2 := hin1.prod (hempty1.prod hempty1)
  have hD1_gates := comp' (fst (encList Boolean.encGate) (encList encNat)) (comp' hD ha1)
  have hstage2 := (IsOraclePPTOn.foldlM_of_bounded_growth (.const false, [])
    (step := fun acc item => realGateStep m item acc)
    (.of_tidy hD1_gates) (.of_tidy hinit2)
    ((isOraclePPTOn_realGateStep m).preprocess'
      (prepare := fun p : Step2Acc m × (Boolean.Op × List ℕ) => (p.2, p.1)) (by fun_prop))
    (fun acc item => realGateStep_growth m item acc)).keep_input
  have hs2_s1 := fst e1 (encStep2Acc m)
  have hs2_acc2 := snd e1 (encStep2Acc m)
  have ha2 := comp' ha1 hs2_s1
  have hk2 := comp' hk ha2
  have hD2_outs := comp' (snd (encList Boolean.encGate) (encList encNat)) (comp' hD ha2)
  have hwires2 := comp' (fst ePi (encPair ePi ePi)) hs2_acc2
  have hot_c2 := comp' (fst ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hs2_acc2)
  have hot_a2 := comp' (snd ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hs2_acc2)
  have hempty2 : ComputableTidilyInPolyTime
      (fun _ : (FamilyRunInput α m n × ((Fin m → List Bool) × (Fin m → List Bool))) × Step2Acc m =>
        (fun _ : Fin m => ([] : List Bool))) e2 ePi :=
    pi fun _ => const []
  have houtItems2 :=
    computableTidilyInPolyTime_buildOutItems m Finset.univ hk2 hD2_outs hwires2 hempty2
  have hinit3 := hot_c2.prod (hot_a2.prod (hempty2.prod hempty2))
  have hstage3 := (IsOraclePPTOn.foldlM_of_bounded_growth
    ((0, fun _ => false, false) : OutItem m)
    (step := fun acc item => realOutStep m item acc)
    (.of_tidy houtItems2) (.of_tidy hinit3)
    ((isOraclePPTOn_realOutStep m).preprocess'
      (prepare := fun p : Step3Acc m × OutItem m => (p.2, p.1)) (by fun_prop))
    (fun acc item => realOutStep_growth m item acc)).keep_input
  have hs3_s1 := comp' hs2_s1 (fst e2 (encStep3Acc m))
  have hs3_acc3 := snd e2 (encStep3Acc m)
  have hx3 := comp' hx1 hs3_s1
  have hr3 := comp' hr1 hs3_s1
  have hc3 := comp' hc1 hs3_s1
  have hin3 := comp' hin1 hs3_s1
  have hpost := computableTidilyInPolyTime_packRealOutput hx3 hr3 hc3 hin3 hs3_acc3
  dsimp only [e0, ePi, eRC, e1, e2, e3] at hstage1 hstage2 hstage3 hpost
  have hres := ((hstage1.bind hstage2).bind hstage3).map hpost
  unfold realRunWord
  simpa only [bind_assoc, bind_map_left, map_bind, Functor.map_map, bind_pure_comp,
    Function.comp_def, Function.flip_def] using hres

private theorem isPPTOn_simRunWord {α : Type} {encA : α ↪ List Bool}
    (m : ℕ) [NeZero m] (I : Finset (Fin m)) {coins n k : α → ℕ}
    {D : α → List (Boolean.Op × List ℕ) × List ℕ}
    (hcoins : ComputableTidilyInPolyTime coins encA encUnary)
    (hn : ComputableTidilyInPolyTime n encA encUnary)
    (hk : ComputableTidilyInPolyTime k encA encUnary)
    (hD : ComputableTidilyInPolyTime D encA Boolean.encCode) :
    IsPPTOn (encFamilySimInput encA m n k I) encBits
      (simRunWord m coins n k D I) := by
  let e0 := encFamilySimInput encA m n k I
  let ePi := encPi (Index := Fin m) encBits
  let eRC := encPair ePi ePi
  let e1 := encPair e0 eRC
  let e2 := encPair e1 (encStep2Acc m)
  let e3 := encPair e2 (encStep3Acc m)
  have ha0 := (encFamilySimInput_index_polyTime encA m n k I ComputableInPolyTime.id').tidy
  have hx0 := computableTidilyInPolyTime_familySimInput_x_bits
    (encA := encA) (m := m) (k := k) (I := I) hn
  have hy0 := computableTidilyInPolyTime_familySimInput_y_bits
    (encA := encA) (m := m) (n := n) (I := I) hk
  have hcoins0 := comp' hcoins ha0
  have hn0 := comp' hn ha0
  have hw1_0 : ∀ i : Fin m, ComputableTidilyInPolyTime
      (fun inp : FamilySimInput α m n k I => if i ∈ I then coins inp.index else 0) e0 encUnary := by
    intro i
    by_cases hi : i ∈ I
    · simpa only [hi, ↓reduceIte] using hcoins0
    · simpa only [hi, ↓reduceIte] using const (encIn := e0) (encMid := encUnary) 0
  have hnc0 := comp' unary_add (hn0.prod hcoins0)
  have hw2_0 := comp' unary_mul (hnc0.prod (const (m - 1)))
  have hstage1 := (isPPTOn_sampleTwoPiBits hw1_0 (fun _ : Fin m => hw2_0)).keep_input
  have hs1_inp := fst e0 eRC
  have hs1_rc := snd e0 eRC
  have ha1 := comp' ha0 hs1_inp
  have hx1 := comp' hx0 hs1_inp
  have hy1 := comp' hy0 hs1_inp
  have hr1 := comp' (fst ePi ePi) hs1_rc
  have hc1 := comp' (snd ePi ePi) hs1_rc
  have hnc1 := comp' hnc0 hs1_inp
  have hin1 := computableTidilyInPolyTime_step1Wires m hnc1 hx1 hr1 hc1
  have hempty1 : ComputableTidilyInPolyTime
      (fun _ : FamilySimInput α m n k I × ((Fin m → List Bool) × (Fin m → List Bool)) =>
        (fun _ : Fin m => ([] : List Bool))) e1 ePi :=
    pi fun _ => const []
  have hinit2 := hin1.prod (hempty1.prod hempty1)
  have hD1_gates := comp' (fst (encList Boolean.encGate) (encList encNat)) (comp' hD ha1)
  have hstage2 := (IsPPTOn.foldlM_of_bounded_growth (.const false, [])
    (step := fun acc item => simGateStep m I item acc)
    (.of_tidy hD1_gates) (.of_tidy hinit2)
    ((isPPTOn_simGateStep m I).preprocess
      (prepare := fun p : Step2Acc m × (Boolean.Op × List ℕ) => (p.2, p.1)) (by fun_prop))
    (fun acc item => simGateStep_growth m I item acc)).keep_input
  have hs2_s1 := fst e1 (encStep2Acc m)
  have hs2_acc2 := snd e1 (encStep2Acc m)
  have ha2 := comp' ha1 hs2_s1
  have hk2 := comp' hk ha2
  have hy2 := comp' hy1 hs2_s1
  have hD2_outs := comp' (snd (encList Boolean.encGate) (encList encNat)) (comp' hD ha2)
  have hwires2 := comp' (fst ePi (encPair ePi ePi)) hs2_acc2
  have hot_c2 := comp' (fst ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hs2_acc2)
  have hot_a2 := comp' (snd ePi ePi) (comp' (snd ePi (encPair ePi ePi)) hs2_acc2)
  have hempty2 : ComputableTidilyInPolyTime
      (fun _ :
        (FamilySimInput α m n k I × ((Fin m → List Bool) × (Fin m → List Bool))) × Step2Acc m =>
        (fun _ : Fin m => ([] : List Bool))) e2 ePi :=
    pi fun _ => const []
  have houtItems2 := computableTidilyInPolyTime_buildOutItems m I hk2 hD2_outs hwires2 hy2
  have hinit3 := hot_c2.prod (hot_a2.prod (hempty2.prod hempty2))
  have hstage3 := (IsPPTOn.foldlM_of_bounded_growth ((0, fun _ => false, false) : OutItem m)
    (step := fun acc item => simOutStep m I item acc)
    (.of_tidy houtItems2) (.of_tidy hinit3)
    ((isPPTOn_simOutStep m I).preprocess
      (prepare := fun p : Step3Acc m × OutItem m => (p.2, p.1)) (by fun_prop))
    (fun acc item => simOutStep_growth m I item acc)).keep_input
  have hs3_s1 := comp' hs2_s1 (fst e2 (encStep3Acc m))
  have hs3_acc3 := snd e2 (encStep3Acc m)
  have hx3 := comp' hx1 hs3_s1
  have hr3 := comp' hr1 hs3_s1
  have hc3 := comp' hc1 hs3_s1
  have hin3 := comp' hin1 hs3_s1
  have hpost := computableTidilyInPolyTime_packSimOutput I hx3 hr3 hc3 hin3 hs3_acc3
  dsimp only [e0, ePi, eRC, e1, e2, e3] at hstage1 hstage2 hstage3 hpost
  have hres := ((hstage1.bind hstage2).bind hstage3).map (ComputableInPolyTime.of_tidy hpost)
  unfold simRunWord
  simpa only [bind_assoc, bind_map_left, map_bind, Functor.map_map, bind_pure_comp,
    Function.comp_def, Function.flip_def] using hres

end PolyTimeRunner

end Cslib.Crypto.Protocols.MPC
