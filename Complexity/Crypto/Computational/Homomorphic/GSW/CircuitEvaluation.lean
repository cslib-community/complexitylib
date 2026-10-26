/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.Evaluation
public import Complexity.Computability.Circuit.Boolean.Layered.Compile
import Complexity.Computability.Circuit.Boolean.Layered.Compile.Correctness
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Homomorphic evaluation of Boolean circuits under GSW

A circuit is compiled into consecutive NAND layers by `Layered.compile`, and every layer is
evaluated on serialized GSW ciphertexts. Constants are the noiseless public ciphertexts
`Flatten(μ · I_N)`, copies forward a wire, and NAND is the serialized `Flatten(I_N - C₁ C₂)`.
The evaluator is deterministic and uses only the dimensions, not the public key.

`BoundedError` is GSW's "B-bounded error" on complete serialized words. A NAND layer multiplies
the bound by at most `N + 1`, where `N = (n + 1) * w`, so a circuit of depth `d`, compiled into
`2 * d` layers, returns a `(N + 1) ^ (2 * d) * B`-bounded ciphertext of its output on
`B`-bounded inputs [GentrySahaiWaters2013, Section 3.3]. Under the strict margin
`4 * m * η * (N + 1) ^ (2 * d) < 2 ^ w` this decrypts correctly for every supported key and
fresh encryption. The margin constant `4` comes from this library's middle-half decoder; it is
not the paper's `q / B > 8 (N + 1) ^ L` [GentrySahaiWaters2013, Section 3.4].

## Main definitions

* `Cslib.Crypto.Homomorphic.GSW.constCiphertext`, `.constSerialized`: noiseless constants.
* `Cslib.Crypto.Homomorphic.GSW.BoundedError`: a complete word with a bounded integer error.
* `Cslib.Crypto.Homomorphic.GSW.evaluateNode`, `.evaluateLayer`, `.evaluateLayers`: layered
  evaluation on serialized ciphertexts, total on malformed inputs.
* `Cslib.Crypto.Homomorphic.GSW.evaluateCircuit`: compile, evaluate and select output `0`.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.boundedError_encryptSerialized`: supported fresh encryptions
  have error bounded by `m * η`.
* `Cslib.Crypto.Homomorphic.GSW.BoundedError.nandSerialized`: NAND turns bounds `B₁, B₂` into
  `B₁ + N * B₂`.
* `Cslib.Crypto.Homomorphic.GSW.boundedError_evaluateCircuit`: the error after a circuit of
  depth `d` is bounded by `(N + 1) ^ (2 * d)` times the input bound.
* `Cslib.Crypto.Homomorphic.GSW.evaluateCircuit_correct`: correctness and exact width on
  supported fresh encryptions under the strict margin.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Sections 3.3 and 3.4]
  [GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Circuits Circuits.Boolean BitString

/-- The noiseless ciphertext `Flatten(μ · I_N)` of a public bit. -/
def constCiphertext (n w : ℕ) (μ : Bool) : Ciphertext n w :=
  flattenMatrix w ((μ.toNat : ZMod (2 ^ w)) • 1)

/-- A noiseless constant satisfies the GSW equation with zero error, under every secret. -/
theorem constCiphertext_hasError {n w : ℕ} (t : Fin n → ZMod (2 ^ w)) (μ : Bool) :
    HasError t (constCiphertext n w μ) μ 0 := by
  unfold HasError constCiphertext
  rw [flattenMatrix_mulVec, _root_.Matrix.smul_mulVec, _root_.Matrix.one_mulVec]
  funext i
  simp

/-- The constant is the bit decomposition of `μ • G`. -/
theorem constCiphertext_eq_decomposeMatrix (n w : ℕ) (μ : Bool) :
    constCiphertext n w μ = decomposeMatrix w ((μ.toNat : ZMod (2 ^ w)) • gadgetMatrix n w) := by
  rw [constCiphertext, flattenMatrix, recomposeMatrix_smul]
  rfl

/-- Write all bits of `Flatten(μ · I_N)` in the ciphertext order of `serializeCiphertext`. -/
def constSerialized (n w : ℕ) (μ : Bool) : List Bool :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range w).flatMap fun k =>
      (List.range (n + 1)).flatMap fun j =>
        lowBits w (if μ ∧ i = j then 2 ^ k else 0)

private theorem constEntry_eq (n w : ℕ) (μ : Bool)
    (i : Fin (n + 1)) (k : Fin w) (j : Fin (n + 1)) :
    (if μ = true ∧ i.val = j.val then 2 ^ k.val else 0) =
      (((μ.toNat : ZMod (2 ^ w)) • gadgetMatrix n w) (i, k) j).val := by
  have hval : ((2 : ZMod (2 ^ w)) ^ k.val).val = 2 ^ k.val := by
    rw [show (2 : ZMod (2 ^ w)) ^ k.val = ((2 ^ k.val : ℕ) : ZMod (2 ^ w)) by simp,
      ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) k.isLt)]
  rw [_root_.Matrix.smul_apply, gadgetMatrix_apply, smul_eq_mul]
  by_cases h : i = j
  · cases μ <;> simp [h, hval]
  · have hv : i.val ≠ j.val := fun hij => h (Fin.ext hij)
    simp [h, hv]

/-- The computed word is the canonical serialization of the typed constant. -/
theorem constSerialized_eq (n w : ℕ) (μ : Bool) :
    constSerialized n w μ = serializeCiphertext (constCiphertext n w μ) := by
  rw [constCiphertext_eq_decomposeMatrix]
  simp only [constSerialized, serializeCiphertext, List.flatMap_def,
    List.map_range_eq_ofFn, lowBits_eq_ofFn, ofFn_blocksEquiv_symm,
    constEntry_eq, decomposeMatrix, bitDecomp]

/-- A constant word has the complete square ciphertext width. -/
@[simp] theorem length_constSerialized (n w : ℕ) (μ : Bool) :
    (constSerialized n w μ).length = ((n + 1) * w) ^ 2 := by
  rw [constSerialized_eq, length_serializeCiphertext]

/-- `ciphertext` is a complete square ciphertext word encrypting `μ` under `secret` whose
integer error has every coordinate bounded by `bound`. This is GSW's "B-bounded error"
[GentrySahaiWaters2013, Section 3.4] for serialized words. It makes no freshness claim. -/
def BoundedError (n w : ℕ) (secret : List Bool) (bound : ℕ) (μ : Bool)
    (ciphertext : List Bool) : Prop :=
  ciphertext.length = ((n + 1) * w) ^ 2 ∧
    ∃ error, HasError (decodeSecret n w secret) (decodeCiphertext n w ciphertext) μ error ∧
      ∀ i, (error i).natAbs ≤ bound

namespace BoundedError

variable {n w : ℕ} {secret : List Bool} {bound bound₁ bound₂ : ℕ} {μ μ₁ μ₂ : Bool}
  {ciphertext left right : List Bool}

/-- A bound may be weakened. -/
theorem mono (h : BoundedError n w secret bound μ ciphertext) {bound' : ℕ}
    (hle : bound ≤ bound') : BoundedError n w secret bound' μ ciphertext := by
  obtain ⟨hlength, error, herror, hbound⟩ := h
  exact ⟨hlength, error, herror, fun i => (hbound i).trans hle⟩

/-- A word with error strictly below a quarter of the modulus decrypts to its plaintext. -/
theorem decryptSerialized_eq (h : BoundedError n w secret bound μ ciphertext) (hw : 0 < w)
    (hmargin : 4 * bound < 2 ^ w) : decryptSerialized n w secret ciphertext = μ := by
  obtain ⟨_, error, herror, hbound⟩ := h
  exact decryptSerialized_eq_of_hasError hw secret ciphertext μ error herror
    (fun i => (Nat.mul_le_mul_left 4 (hbound i)).trans_lt hmargin)

/-- NAND of `B₁`- and `B₂`-bounded words is `B₁ + N * B₂`-bounded, with `N = (n + 1) * w`
[GentrySahaiWaters2013, Section 3.3]. -/
theorem nandSerialized (hleft : BoundedError n w secret bound₁ μ₁ left)
    (hright : BoundedError n w secret bound₂ μ₂ right) :
    BoundedError n w secret (bound₁ + (n + 1) * w * bound₂) (!(μ₁ && μ₂))
      (GSW.nandSerialized n w left right) := by
  obtain ⟨_, error₁, herror₁, hbound₁⟩ := hleft
  obtain ⟨_, error₂, herror₂, hbound₂⟩ := hright
  refine ⟨length_nandSerialized n w left right, _,
    nandSerialized_hasError secret left right μ₁ μ₂ error₁ error₂ herror₁ herror₂, fun i => ?_⟩
  simpa using nandError_natAbs_le _ μ₂ error₁ error₂ hbound₁ hbound₂ i

end BoundedError

/-- A noiseless constant is `0`-bounded under every secret word. -/
theorem boundedError_constSerialized (n w : ℕ) (secret : List Bool) (μ : Bool) :
    BoundedError n w secret 0 μ (constSerialized n w μ) := by
  refine ⟨length_constSerialized n w μ, 0, ?_, fun i => by simp⟩
  rw [constSerialized_eq, decode_serializeCiphertext]
  exact constCiphertext_hasError _ μ

/-- Every supported fresh encryption under a supported key has error bounded by `m * η`. -/
theorem boundedError_encryptSerialized {n m w η : ℕ} {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGenSerialized n m w η)).support) (μ : Bool)
    {ciphertext : List Bool}
    (hciphertext : ciphertext ∈ (ProbComp.eval (encryptSerialized n m w keys.1 μ)).support) :
    BoundedError n w keys.2 (m * η) μ ciphertext := by
  rw [eval_keyGenSerialized, PMF.mem_support_map_iff] at hkeys
  obtain ⟨typedKeys, htypedKeys, rfl⟩ := hkeys
  rw [eval_encryptSerialized_serializePublicMatrix, PMF.mem_support_map_iff] at hciphertext
  obtain ⟨typedCiphertext, htypedCiphertext, rfl⟩ := hciphertext
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htypedKeys
  obtain ⟨inputs, hinputs, rfl⟩ := htypedKeys
  obtain ⟨coins, rfl⟩ := (mem_support_encrypt_iff _ _ _).mp htypedCiphertext
  refine ⟨length_serializeCiphertext _, encryptionError coins inputs.error, ?_, fun i => ?_⟩
  · rw [decode_serializeSecret, decode_serializeCiphertext]
    exact encryptWithCoins_hasError inputs.publicPart inputs.secret inputs.error μ coins
  · simpa using encryptionError_natAbs_le coins inputs.error
      ((mem_support_sampleKeyInputs_iff _ _ _ _ _).mp hinputs) i

/-- Evaluate one layered node on serialized ciphertexts. Copies are cut to the ciphertext width,
which leaves every complete ciphertext unchanged and bounds malformed wires. -/
def evaluateNode (n w : ℕ) (wires : List (List Bool)) : Layered.Node → List Bool
  | .const μ => constSerialized n w μ
  | .copy i => (wires.getD i []).take (((n + 1) * w) ^ 2)
  | .nand i j => nandSerialized n w (wires.getD i []) (wires.getD j [])

/-- Evaluate every node of a layer on the preceding wires. -/
def evaluateLayer (n w : ℕ) (wires : List (List Bool)) (layer : List Layered.Node) :
    List (List Bool) :=
  layer.map (evaluateNode n w wires)

/-- Evaluate the layers in order, starting from the input ciphertexts. -/
def evaluateLayers (n w : ℕ) (wires : List (List Bool)) (layers : List (List Layered.Node)) :
    List (List Bool) :=
  layers.foldl (evaluateLayer n w) wires

/-- Compile the circuit into NAND layers, evaluate them, and return designated output `0`.
Evaluation needs only the dimensions; no public key or evaluation key is read. -/
def evaluateCircuit (n w : ℕ) (C : Σ k, Circuit signature k 1) (inputs : List (List Bool)) :
    List Bool :=
  let compiled := Layered.compile C.1 C.2.code
  (evaluateLayers n w inputs compiled.1).getD (compiled.2.headD 0) []

@[simp] theorem evaluateLayers_nil (n w : ℕ) (wires : List (List Bool)) :
    evaluateLayers n w wires [] = wires := rfl

@[simp] theorem evaluateLayers_cons (n w : ℕ) (wires : List (List Bool))
    (layer : List Layered.Node) (layers : List (List Layered.Node)) :
    evaluateLayers n w wires (layer :: layers) =
      evaluateLayers n w (evaluateLayer n w wires layer) layers := rfl

variable {n w : ℕ} {secret : List Bool} {bound : ℕ}

/-- One valid node multiplies the error bound by at most `N + 1`. -/
theorem boundedError_evaluateNode {bits : List Bool} {wires : List (List Bool)}
    (h : List.Forall₂ (BoundedError n w secret bound) bits wires) (node : Layered.Node)
    (hnode : node.Valid bits.length) :
    BoundedError n w secret (((n + 1) * w + 1) * bound) (node.eval bits)
      (evaluateNode n w wires node) := by
  cases node with
  | const μ => exact (boundedError_constSerialized n w secret μ).mono (Nat.zero_le _)
  | copy i =>
    have hi := h.getD hnode false []
    have htake : (wires.getD i []).take (((n + 1) * w) ^ 2) = wires.getD i [] :=
      List.take_of_length_le hi.1.le
    simp only [evaluateNode, Layered.Node.eval, htake]
    exact hi.mono (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  | nand i j =>
    have h' := (h.getD hnode.1 false []).nandSerialized (h.getD hnode.2 false [])
    simp only [evaluateNode, Layered.Node.eval]
    exact h'.mono (le_of_eq (by ring))

/-- A valid layer multiplies the error bound by at most `N + 1`. -/
theorem forall₂_evaluateLayer {bits : List Bool} {wires : List (List Bool)}
    (h : List.Forall₂ (BoundedError n w secret bound) bits wires)
    {layer : List Layered.Node} (hlayer : ∀ node ∈ layer, node.Valid bits.length) :
    List.Forall₂ (BoundedError n w secret (((n + 1) * w + 1) * bound))
      (Layered.evalLayer bits layer) (evaluateLayer n w wires layer) := by
  simp only [Layered.evalLayer, evaluateLayer, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff, List.forall₂_same]
  exact fun node hnode => boundedError_evaluateNode h node (hlayer node hnode)

/-- A well-formed schedule of `L` layers multiplies the error bound by at most `(N + 1) ^ L`
[GentrySahaiWaters2013, Section 3.3]. Copy layers are counted although they add no error. -/
theorem forall₂_evaluateLayers {bits : List Bool} {wires : List (List Bool)}
    (h : List.Forall₂ (BoundedError n w secret bound) bits wires)
    {layers : List (List Layered.Node)} (hlayers : Layered.WellFormed bits.length layers) :
    List.Forall₂ (BoundedError n w secret (((n + 1) * w + 1) ^ layers.length * bound))
      (Layered.eval bits layers) (evaluateLayers n w wires layers) := by
  induction layers generalizing bits wires bound with
  | nil => simpa using h
  | cons layer layers ih =>
    have hnext := ih (forall₂_evaluateLayer h hlayers.1)
      (by simpa only [Layered.length_evalLayer] using hlayers.2)
    simpa only [Layered.eval_cons, evaluateLayers_cons, List.length_cons, pow_succ,
      Nat.mul_assoc] using hnext

/-- A circuit of depth `d` evaluated on `B`-bounded inputs returns a
`(N + 1) ^ (2 * d) * B`-bounded ciphertext of its output, with `N = (n + 1) * w`. The inputs may
themselves be outputs of earlier evaluations. -/
theorem boundedError_evaluateCircuit (C : Σ k, Circuit signature k 1) {bits : List Bool}
    {wires : List (List Bool)} (hbits : bits.length = C.1)
    (h : List.Forall₂ (BoundedError n w secret bound) bits wires) :
    BoundedError n w secret (((n + 1) * w + 1) ^ (2 * C.2.depth) * bound)
      (C.2.eval interpretation (BitString.ofList C.1 bits) 0) (evaluateCircuit n w C wires) := by
  have hbitsEq : List.ofFn (BitString.ofList C.1 bits) = bits := BitString.ofFn_ofList hbits
  have hlayers := forall₂_evaluateLayers h (layers := (Layered.compile C.1 C.2.code).1)
    (by simpa only [hbits] using Layered.wellFormed_compile C.2)
  rw [Layered.length_compile] at hlayers
  have hselect := Layered.select_eval_compile C.2 (BitString.ofList C.1 bits)
  rw [hbitsEq] at hselect
  have hone : (Layered.compile C.1 C.2.code).2.length = 1 := by
    simpa only [Layered.length_select, List.length_ofFn] using congrArg List.length hselect
  obtain ⟨index, hindex⟩ := List.length_eq_one_iff.mp hone
  have hvalid := Layered.outputs_valid_compile C.2 index (by
    rw [hindex]
    exact List.mem_singleton_self index)
  rw [hindex] at hselect
  simp only [Layered.select, List.map_cons, List.map_nil, List.ofFn_succ, List.ofFn_zero,
    List.cons.injEq, and_true] at hselect
  have hwire := hlayers.getD (i := index) (by
    simpa only [Layered.length_eval, hbits] using hvalid) false []
  rw [hselect] at hwire
  simpa only [evaluateCircuit, hindex, List.headD_cons] using hwire

/-- GSW circuit evaluation is correct on supported fresh encryptions under a supported key,
when `4 * m * η * (N + 1) ^ (2 * d) < 2 ^ w` for the circuit's depth `d`. The output also has
the exact square ciphertext width. This is the bounded-depth correctness of
[GentrySahaiWaters2013, Sections 3.3 and 3.4] for the library's decoder. -/
theorem evaluateCircuit_correct {m η : ℕ} (hw : 0 < w) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (keyGenSerialized n m w η)).support)
    (C : Σ k, Circuit signature k 1)
    (hmargin : 4 * m * η * ((n + 1) * w + 1) ^ (2 * C.2.depth) < 2 ^ w)
    {bits : List Bool} {inputs : List (List Bool)} (hbits : bits.length = C.1)
    (hinputs : List.Forall₂
      (fun μ c => c ∈ (ProbComp.eval (encryptSerialized n m w keys.1 μ)).support) bits inputs) :
    (evaluateCircuit n w C inputs).length = ((n + 1) * w) ^ 2 ∧
      decryptSerialized n w keys.2 (evaluateCircuit n w C inputs) =
        C.2.eval interpretation (BitString.ofList C.1 bits) 0 := by
  have h := boundedError_evaluateCircuit C hbits
    (hinputs.imp fun μ c hc => boundedError_encryptSerialized hkeys μ hc)
  refine ⟨h.1, h.decryptSerialized_eq hw ?_⟩
  calc
    4 * (((n + 1) * w + 1) ^ (2 * C.2.depth) * (m * η)) =
        4 * m * η * ((n + 1) * w + 1) ^ (2 * C.2.depth) := by ring
    _ < 2 ^ w := hmargin

end Cslib.Crypto.Homomorphic.GSW
