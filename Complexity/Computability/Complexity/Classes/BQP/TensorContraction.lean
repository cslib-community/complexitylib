/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BQP.Time
public import Complexity.Computability.Circuit.Quantum.PathNetworkPolyTime
public import Complexity.Computability.Complexity.Classes.CountingSimulation.FastLeaves
public import Complexity.Computability.Complexity.Classes.Time
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
public import Complexity.Computability.GenericRAM.Native.ExpTimePolySpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Foundations.Data.Nat.SqrtLog.Linear

/-!
# Quantum circuits by tensor contraction: quantum time `T` in `DTIME[2 ^ O(T / √log T)]`

The probability that the final measurement of a circuit of `L` gates over the Hadamard, NOT, CNOT
and Toffoli gates finds every qubit of a list `S` in state `1` is `onesGap S / 2 ^ h`, where `h` is
the number of Hadamard gates (`Cslib.Quantum.onesProb_eq_onesGap`); acceptance is the case
`S = [0]`. The projected gap is the contraction of the network of the circuit and its mirror copy
(`Cslib.Quantum.PathNetwork.contraction_network`), and over `ℕ`, with the Hadamard sign
`2 ^ (h + 1) - 1`, its residue modulo `2 ^ (h + 1)`
(`Cslib.Quantum.PathNetwork.contraction_network_mod`). The network has `s = 4 N` edges for
`N ≤ 3 L` occurrences of qubits in gates, degree at most six and a bipartition, so it is admissible
for the contraction algorithm of Theorem D.1 of [OpenAI2026ETH]
(`CountingSimulation.fastContractionAlgorithm`) at size `s`, which contracts it in time
`2 ^ O(s / √⌊log₂ s⌋)` times a polynomial and in polynomial space. The width of the circuit does
not enter the exponent: qubits that no gate touches cost nothing.

So the projected gaps of polynomial-time computed circuits are computed by one machine in time
`2 ^ (A (L + 1) / √⌊log₂ (L + 2)⌋)` times a polynomial in the input length, and in polynomial space
(`QuantumContraction.exists_computableInO_gapValue`), and so is any polynomial-time rule applied to
two of them (`QuantumContraction.exists_computableInO_rule`). The gaps are exact, so a rule can
test a probability for zero or compare two probabilities. For a uniform family with `O(T)` gates
and `max n 2 ≤ T n`, a problem decided by such a rule lies in `⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`,
with a joint polynomial space bound `T ^ d`
(`QuantumContraction.exists_decidableInTimeAndSpace_of_onesProb`):

* `BQTIME[T]`: the acceptance gap `g` against the gap `2 ^ h` of no condition, `2 ^ h < 2 g`;
* `NQTIME[T]`: the acceptance gap is positive;
* `EQTIME[T]`, which lies in `NQTIME[T]`;
* `PostBQTIME[T]`: the gap `g` of qubits `0` and `1` against the gap `g'` of qubit `1`, `g' < 2 g`.

No time-constructibility of `T` is needed, since the machine never computes `T`. The textbook
characterizations `NQP = coC₌P` [FennerGreenHomerPruim1999] and `PostBQP = PP`
[Aaronson2005Postselection] would lose a polynomial in `T`. The novelty of these bounds has not
been established; a limited search found no direct simulation of these classes in this time.

## Main definitions

* `Cslib.Complexity.QuantumContraction.gapValue`: the projected gap as the simulator computes it.

## Main results

* `Cslib.Quantum.PathNetwork.explicitAdmissible_network`: the network is admissible.
* `Cslib.Complexity.QuantumContraction.gapValue_eq`: the simulator computes the projected gap.
* `Cslib.Complexity.QuantumContraction.exists_computableInO_gapValue`,
  `Cslib.Complexity.QuantumContraction.exists_computableInO_rule`: the simulator and its
  resources.
* `Cslib.Complexity.QuantumContraction.exists_decidableInTimeAndSpace_of_onesProb`: deciding by two
  projected gaps.
* `Cslib.Complexity.QuantumContraction.BQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `Cslib.Complexity.QuantumContraction.NQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `Cslib.Complexity.QuantumContraction.EQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `Cslib.Complexity.QuantumContraction.PostBQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  with the joint forms `exists_decidableInTimeAndSpace_of_mem_BQTIME`, `…_NQTIME` and
  `…_PostBQTIME`: the class containments.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
* [S. Fenner, F. Green, S. Homer, R. Pruim, *Determining acceptance possibility for a quantum
  computation is hard for the polynomial hierarchy*][FennerGreenHomerPruim1999]
* [S. Aaronson, *Quantum computing, postselection, and probabilistic
  polynomial-time*][Aaronson2005Postselection]
-/

public section

namespace Cslib.Quantum.PathNetwork

open Cslib.Circuits.Frontier Cslib.Complexity.CountingSimulation

/-- The qubits of a well-formed gate code are distinct. -/
theorem nodup_qubits {m : ℕ} {g : GateCode} (h : g.WellFormed m) : (qubits g).Nodup := by
  obtain ⟨_ | _, t, cs⟩ := g
  · exact h.2.1
  · simp [qubits, h.2]

/-- **The network is admissible** at size `4 N`, its number of edges, with constant `6`, for a
nonempty list of well-formed gate codes and any measured qubits. -/
theorem explicitAdmissible_network (neg : ℕ) (S : List ℕ) (X : List Bool) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) (hne : gs ≠ []) :
    ExplicitAdmissible 6 (4 * (occurrences gs).length) (network neg S X gs) := by
  have h3 : ∀ g ∈ gs, (qubits g).length ≤ 3 := fun g hg => length_qubits_le_three (hgs g hg)
  have hL : 1 ≤ gs.length := List.length_pos_iff.mpr hne
  have hLN := length_le_length_occurrences gs
  have hlog : 1 ≤ Nat.log 2 (4 * (occurrences gs).length) := Nat.log_pos (by norm_num) (by omega)
  refine ⟨isRowsFirstBipartite_network neg S X fun g hg => nodup_qubits (hgs g hg), ?_, ?_, ?_,
    length_table_network neg S X h3, ?_⟩
  · rw [numEdges_network]
    omega
  · exact (maxDegree_network_le neg S X h3).trans (by omega)
  · rw [length_vertices_network]
    omega
  · rw [numEdges_network]
    omega

end Cslib.Quantum.PathNetwork

namespace Cslib.Complexity.QuantumContraction

open Quantum Quantum.PathNetwork Cslib.Circuits.Frontier Turing.MultiTapeTM Cslib.GenericRAM
  CountingSimulation ComputableInPolyTime

/-! ### The simulator -/

/-- The circuits handed to the contraction algorithm: those with at least one gate. -/
@[expose] def guard (gs : List GateCode) : Bool := !gs.isEmpty

/-- The input of the contraction algorithm: the precision `h + 1`, for `h` Hadamard gates, and the
network with the measured qubits `S` and Hadamard sign `2 ^ (h + 1) - 1` on the input register
`X`. -/
@[expose] def contractionInput (S : List ℕ) (gs : List GateCode) (X : List Bool) :
    ℕ × ℕ × ExplicitTensorNetwork ℕ :=
  (hadamardCount gs + 1, network (2 ^ (hadamardCount gs + 1) - 1 : ℕ) S X gs)

/-- The answer for a circuit without gates: whether every qubit of `S` reads one in `X`. -/
@[expose] def fallback (S : List ℕ) (X : List Bool) : ℕ :=
  if S.all fun j => X.getD j false then 1 else 0

/-- **The projected gap as the simulator computes it**: the residue of the contraction of the
network modulo `2 ^ (h + 1)`, or the bits of the qubits of `S` for a circuit without gates. -/
@[expose] def gapValue (S : List ℕ) (gs : List GateCode) (X : List Bool) : ℕ :=
  if guard gs then
    let (precision, _, network) := contractionInput S gs X
    network.contraction % 2 ^ precision
  else fallback S X

/-- **The simulator computes the projected gap** of well-formed gate codes on the register `X`. -/
theorem gapValue_eq (S : List ℕ) {X : List Bool} {gs : List GateCode}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) : gapValue S gs X = (onesGap S gs X).toNat := by
  unfold gapValue
  split
  · exact contraction_network_mod S X gs hgs (Nat.lt_succ_self _)
  · next hg =>
    obtain rfl : gs = [] := by simpa [guard] using hg
    simp only [fallback, onesGap, hadamardCount_nil, onesTerm, pathRun, List.ofFn_zero,
      List.foldl_nil, true_and, Bool.xor_self, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl

/-! ### Resources -/

/-- The exponent of the contraction is at most `12 K (L + 1) / √⌊log₂ (L + 2)⌋` for `L` gates. -/
private theorem exponent_le (K : ℕ) {gs : List GateCode} {m : ℕ}
    (hgs : ∀ g ∈ gs, g.WellFormed m) (hne : gs ≠ []) :
    K * (4 * (occurrences gs).length) / Nat.sqrt (Nat.log 2 (4 * (occurrences gs).length)) ≤
      12 * K * (gs.length + 1) / Nat.sqrt (Nat.log 2 (gs.length + 2)) := by
  have hL : 1 ≤ gs.length := List.length_pos_iff.mpr hne
  have hLN := length_le_length_occurrences gs
  have hN3 := length_occurrences_le hgs
  refine Nat.div_le_div ?_ (Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega))) ?_
  · have : K * (4 * (occurrences gs).length) ≤ K * (12 * (gs.length + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · exact Nat.sqrt_eq_zero.not.mpr (Nat.log_pos (by norm_num) (by omega)).ne'

section Machine

variable {α : Type} {enc : α ↪ List Bool} {gs : α → List GateCode} {X : α → List Bool}

/-- **The simulator as a certificate**: for polynomial-time computed measured qubits `S a` and
gate codes `gs a`, well formed on the polynomial-time computed register `X a`, the projected gap
is computed in time `2 ^ (A (L + 1) / √⌊log₂ (L + 2)⌋)` times a polynomial and in polynomial
space. -/
theorem exists_expTimePolySpace_gapValue {S : α → List ℕ}
    (hS : ComputableInPolyTime S enc (encList encUnary))
    (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits) (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length) :
    ∃ (A : ℕ) (c : NativeCertificate (fun a => gapValue (S a) (gs a) (X a)) enc encNat),
      c.ExpTimePolySpace fun a =>
        A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2)) := by
  obtain ⟨K, hK⟩ := fastContractionAlgorithm.bound 6 1
  -- the polynomial-time parts
  have hh : ComputableInPolyTime (fun a => hadamardCount (gs a)) enc encUnary := by
    simp only [hadamardCount_eq_countP]
    fun_prop
  have hguard : ComputableInPolyTime (fun a => guard (gs a)) enc encBool := by
    unfold guard
    fun_prop
  have hinput : ComputableInPolyTime (fun a => contractionInput (S a) (gs a) (X a)) enc
      (encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)) :=
    (unary_to_binary.comp (unary_add' hh (const 1))).prod (computableInPolyTime_network
      (binary_sub' (binary_pow' (const 2) (unary_add' hh (const 1))) (const 1)) hS hX hgs)
  have hfb : ComputableInPolyTime (fun a => fallback (S a) (X a)) enc encNat :=
    ite_decide (decide_eq' (allWithInput hS (bitsGetDWithInput (hX.comp (fst _ _)) (snd _ _)
      false)) (const true)) (const 1) (const 0)
  -- the machine
  let cv : NativeCertificate (fun a => gapValue (S a) (gs a) (X a)) enc encNat :=
    (NativeCertificate.branch (NativeCertificate.ofPolyTime hguard)
      (fastContractionAlgorithm.certificate.comp (NativeCertificate.ofPolyTime hinput))
      (NativeCertificate.ofPolyTime hfb)).congr fun _ => rfl
  refine ⟨12 * K, cv, ?_⟩
  -- polynomial bounds
  have hpg := NativeCertificate.ofPolyTime_isPolynomial hguard
  have hpi := NativeCertificate.ofPolyTime_isPolynomial hinput
  have hpf := NativeCertificate.ofPolyTime_isPolynomial hfb
  obtain ⟨cg, dg, htg⟩ := hpg.1.exists_le
  obtain ⟨cg', dg', hsg⟩ := hpg.2.exists_le
  obtain ⟨ci, di, hti⟩ := hpi.1.exists_le
  obtain ⟨ci', di', hsi⟩ := hpi.2.exists_le
  obtain ⟨cf, df, htf⟩ := hpf.1.exists_le
  obtain ⟨cf', df', hsf⟩ := hpf.2.exists_le
  obtain ⟨p, q, hlen⟩ := hinput.polyBounded_length.exists_le
  -- the contraction on guarded inputs
  have hinlen (a : α) : (((encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork))
      (contractionInput (S a) (gs a) (X a))).length + 1) ^ K ≤
        (p + 1) ^ K * ((enc a).length + 1) ^ (q * K) := by
    have h1 := hlen a
    have h2 : 1 ≤ ((enc a).length + 1) ^ q := Nat.one_le_pow _ _ (Nat.le_add_left 1 _)
    calc _ ≤ ((p + 1) * ((enc a).length + 1) ^ q) ^ K := Nat.pow_le_pow_left (by nlinarith) K
      _ = _ := by rw [mul_pow, pow_mul]
  have hfast (a : α) (hga : guard (gs a) = true) :
      fastContractionAlgorithm.certificate.time (contractionInput (S a) (gs a) (X a)) ≤
          K * (p + 1) ^ K *
            (2 ^ (12 * K * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
              ((enc a).length + 1) ^ (q * K)) ∧
        fastContractionAlgorithm.certificate.space (contractionInput (S a) (gs a) (X a)) ≤
          K * (p + 1) ^ K * ((enc a).length + 1) ^ (q * K) := by
    have hne : gs a ≠ [] := by simpa [guard] using hga
    have hL : 1 ≤ (gs a).length := List.length_pos_iff.mpr hne
    have hLN := length_le_length_occurrences (gs a)
    have hhL : hadamardCount (gs a) ≤ (gs a).length := by
      rw [hadamardCount_eq_countP]
      exact List.countP_le_length
    have hb := hK (4 * (occurrences (gs a)).length) (hadamardCount (gs a) + 1)
      (network (2 ^ (hadamardCount (gs a) + 1) - 1 : ℕ) (S a) (X a) (gs a)) (by omega) (by omega)
      (by omega) (explicitAdmissible_network _ (S a) (X a) (hwf a) hne)
    constructor
    · refine hb.1.trans ?_
      calc _ ≤ K * ((p + 1) ^ K * ((enc a).length + 1) ^ (q * K)) *
            2 ^ (12 * K * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (hinlen a))
              (Nat.pow_le_pow_right (by norm_num) (exponent_le K (hwf a) hne))
        _ = _ := by ring
    · exact hb.2.trans ((Nat.mul_le_mul_left K (hinlen a)).trans (Nat.mul_assoc _ _ _).ge)
  -- the totals
  set d := dg + di + df + dg' + di' + df' + q * K
  refine ⟨cg + ci + cf + cg' + ci' + cf' + K * (p + 1) ^ K, d, fun a => ?_⟩
  set Y := ((enc a).length + 1) ^ d
  set Z := 2 ^ (12 * K * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2)))
  have hY {e : ℕ} (he : e ≤ d) : ((enc a).length + 1) ^ e ≤ Y :=
    Nat.pow_le_pow_right (Nat.le_add_left 1 _) he
  have hZ : Y ≤ Z * Y := Nat.le_mul_of_pos_left Y (Nat.two_pow_pos _)
  change (NativeCertificate.ofPolyTime hguard).time a + (if guard (gs a) then
        (NativeCertificate.ofPolyTime hinput).time a +
          fastContractionAlgorithm.certificate.time (contractionInput (S a) (gs a) (X a))
        else (NativeCertificate.ofPolyTime hfb).time a) ≤ _ ∧
      (NativeCertificate.ofPolyTime hguard).space a + (if guard (gs a) then
        (NativeCertificate.ofPolyTime hinput).space a +
          fastContractionAlgorithm.certificate.space (contractionInput (S a) (gs a) (X a))
        else (NativeCertificate.ofPolyTime hfb).space a) ≤ _
  have e1 := (htg a).trans (Nat.mul_le_mul_left cg ((hY (e := dg) (by omega)).trans hZ))
  have e2 := (hti a).trans (Nat.mul_le_mul_left ci ((hY (e := di) (by omega)).trans hZ))
  have e3 := (htf a).trans (Nat.mul_le_mul_left cf ((hY (e := df) (by omega)).trans hZ))
  have e1' := (hsg a).trans (Nat.mul_le_mul_left cg' (hY (e := dg') (by omega)))
  have e2' := (hsi a).trans (Nat.mul_le_mul_left ci' (hY (e := di') (by omega)))
  have e3' := (hsf a).trans (Nat.mul_le_mul_left cf' (hY (e := df') (by omega)))
  have hqK : ((enc a).length + 1) ^ (q * K) ≤ Y := hY (by omega)
  split
  · next hga =>
    have e4 := (hfast a hga).1.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left Z hqK))
    have e4' := (hfast a hga).2.trans (Nat.mul_le_mul_left _ hqK)
    constructor
    · calc _ ≤ cg * (Z * Y) + (ci * (Z * Y) + K * (p + 1) ^ K * (Z * Y)) :=
            Nat.add_le_add e1 (Nat.add_le_add e2 e4)
        _ ≤ _ := by
          rw [show cg * (Z * Y) + (ci * (Z * Y) + K * (p + 1) ^ K * (Z * Y)) =
            (cg + ci + K * (p + 1) ^ K) * Z * Y by ring]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    · calc _ ≤ cg' * Y + (ci' * Y + K * (p + 1) ^ K * Y) :=
            Nat.add_le_add e1' (Nat.add_le_add e2' e4')
        _ ≤ _ := by
          rw [show cg' * Y + (ci' * Y + K * (p + 1) ^ K * Y) =
            (cg' + ci' + K * (p + 1) ^ K) * Y by ring]
          exact Nat.mul_le_mul_right _ (by omega)
  · constructor
    · calc _ ≤ cg * (Z * Y) + cf * (Z * Y) := Nat.add_le_add e1 e3
        _ ≤ _ := by
          rw [show cg * (Z * Y) + cf * (Z * Y) = (cg + cf) * Z * Y by ring]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    · calc _ ≤ cg' * Y + cf' * Y := Nat.add_le_add e1' e3'
        _ ≤ _ := by
          rw [show cg' * Y + cf' * Y = (cg' + cf') * Y by ring]
          exact Nat.mul_le_mul_right _ (by omega)

/-- **The simulator.** For polynomial-time computed measured qubits `S a` and gate codes `gs a`,
well formed on the polynomial-time computed register `X a`, one machine computes
`gapValue (S a) (gs a) (X a)`, the projected gap (`QuantumContraction.gapValue_eq`), in time
`2 ^ (A (L + 1) / √⌊log₂ (L + 2)⌋)` times a polynomial in the input length and in polynomial
space, where `L` is the number of gates. -/
theorem exists_computableInO_gapValue {S : α → List ℕ}
    (hS : ComputableInPolyTime S enc (encList encUnary))
    (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits)
    (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length) :
    ∃ A e : ℕ, ComputableInO (fun a => gapValue (S a) (gs a) (X a)) enc encNat
      (fun a => 2 ^ (A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
        ((enc a).length + 1) ^ e)
      (fun a => ((enc a).length + 1) ^ e) := by
  obtain ⟨A, c, hc⟩ := exists_expTimePolySpace_gapValue hS hgs hX hwf
  obtain ⟨e, he⟩ := hc.computableInO
  exact ⟨A, e, he⟩

/-- **Two projected gaps with polynomial-time postprocessing.** For polynomial-time computed lists
`S a` and `P a` of measured qubits and gate codes `gs a`, well formed on the polynomial-time
computed register `X a`, one machine computes `rule (gapValue (S a) …, gapValue (P a) …)`, for a
polynomial-time `rule`, in time `2 ^ (A (L + 1) / √⌊log₂ (L + 2)⌋)` times a polynomial in the
input length and in polynomial space, where `L` is the number of gates. With `P a = []`, whose
projected gap is `2 ^ h` (`Cslib.Quantum.onesGap_nil_eq_two_pow`), the rule sees a probability
and its denominator; with `P a` a postselected event, a conditional probability. -/
theorem exists_computableInO_rule {S P : α → List ℕ}
    (hS : ComputableInPolyTime S enc (encList encUnary))
    (hP : ComputableInPolyTime P enc (encList encUnary))
    (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits) (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length)
    {β : Type} {encβ : β ↪ List Bool} {rule : ℕ × ℕ → β}
    (hrule : ComputableInPolyTime rule (encPair encNat encNat) encβ) :
    ∃ A e : ℕ, ComputableInO
      (fun a => rule (gapValue (S a) (gs a) (X a), gapValue (P a) (gs a) (X a))) enc encβ
      (fun a => 2 ^ (A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
        ((enc a).length + 1) ^ e)
      (fun a => ((enc a).length + 1) ^ e) := by
  obtain ⟨A, c, hc⟩ := exists_expTimePolySpace_gapValue hS hgs hX hwf
  obtain ⟨A', c', hc'⟩ := exists_expTimePolySpace_gapValue hP hgs hX hwf
  have hcc := ((hc.prod hc').mono (E' := fun a =>
    (A + A') * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) fun a =>
      Nat.div_add_div_le_add_div.trans (Nat.div_le_div_right (by rw [Nat.add_mul]))).comp_ofPolyTime
    hrule
  obtain ⟨e, he⟩ := hcc.computableInO
  exact ⟨A + A', e, he⟩

end Machine

/-- **Probabilities from the simulator**: for well-formed codes on `m` qubits and an input `x` of
length at most `m`, the probability that every qubit of `S` reads `1` is `gapValue S / 2 ^ h` on the
padded register. -/
theorem onesProb_eq_gapValue {m : ℕ} {gs : List GateCode} (hgs : ∀ g ∈ gs, g.WellFormed m)
    (S : List ℕ) {x : List Bool} (hx : x.length ≤ m) :
    onesProb m gs S x =
      (gapValue S gs (x ++ List.replicate (m - x.length) false) : ℝ) / 2 ^ hadamardCount gs := by
  have hlen : (x ++ List.replicate (m - x.length) false).length = m := by simp; omega
  have hgs' : ∀ g ∈ gs, g.WellFormed (x ++ List.replicate (m - x.length) false).length := by
    rw [hlen]
    exact hgs
  rw [onesProb_eq_onesGap gs hgs, ofFn_inputState hx, gapValue_eq S hgs']
  congr 1
  have := Int.toNat_of_nonneg (onesGap_nonneg_and_le S gs hgs').1
  exact_mod_cast this.symm

/-! ### The class containments -/

variable {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}

/-- **Deciding by two projected gaps in time `2 ^ O(T / √log T)` and space `T ^ O(1)`.** For `T`
with `max n 2 ≤ T n`, a uniform family with `O(T)` gates and lists `S` and `P` of measured qubits,
a problem is decided by one deterministic machine within time `2 ^ (C T n / √⌊log₂ (T n)⌋)` and
workspace `T n ^ d` when a polynomial-time `rule` decides it from any two numerators `g` and `g'`
over a common power of two of the probabilities that the qubits of `S` and of `P` read `1`. -/
theorem exists_decidableInTimeAndSpace_of_onesProb (hTn : ∀ n, max n 2 ≤ T n)
    {F : UniformCircuitFamily} {c₁ c₂ : ℕ} (hgates : ∀ n, (F.gates n).length ≤ c₁ * T n + c₂)
    (S P : List ℕ) {rule : ℕ × ℕ → Bool}
    (hrule : ComputableInPolyTime rule (encPair encNat encNat) encBool) {L : Set α}
    (hL : ∀ a (g g' r : ℕ), F.onesProb S (enc a) = g / 2 ^ r →
      F.onesProb P (enc a) = g' / 2 ^ r → (a ∈ L ↔ rule (g, g') = true)) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  have hgates' := F.computableInPolyTime_gates
  have hwidth := F.computableInPolyTime_width
  let gs : α → List GateCode := fun a => F.gates (enc a).length
  let X : α → List Bool := fun a =>
    enc a ++ List.replicate (F.width (enc a).length - (enc a).length) false
  have hgs : ComputableInPolyTime gs enc (encList encGateCode) := by dsimp only [gs]; fun_prop
  have henc : ComputableInPolyTime (fun a => enc a) enc encBits := of_eq fun _ => rfl
  have hX : ComputableInPolyTime X enc encBits := by dsimp only [X]; fun_prop
  have hwf (a : α) : ∀ g ∈ gs a, g.WellFormed (X a).length := by
    have : (X a).length = F.width (enc a).length := by
      have := F.le_width (enc a).length
      simp only [X, List.length_append, List.length_replicate]
      omega
    rw [this]
    exact F.wellFormed _
  obtain ⟨A, e, hc⟩ := exists_computableInO_rule (const S) (const P) hgs hX hwf hrule
  obtain ⟨K, hK, -⟩ := hc
  -- correctness
  have hcorrect (a : α) :
      a ∈ L ↔ rule (gapValue S (gs a) (X a), gapValue P (gs a) (X a)) = true :=
    hL a _ _ _ (onesProb_eq_gapValue (F.wellFormed _) S (F.le_width _))
      (onesProb_eq_gapValue (F.wellFormed _) P (F.le_width _))
  -- the bounds
  set C₀ := 2 * A * (c₁ + c₂ + 2) + 2 * e
  set D₀ := 2 * A * (c₁ + c₂ + 2) + 3 * A
  refine ⟨(K * 2 ^ D₀ + K + 1) * (C₀ + 1), K + K + 2 * e,
    decidableInTimeAndSpace_iff.mpr ⟨_, hK.mono (fun a => ?_) (fun a => ?_), hcorrect⟩⟩
  all_goals
    have hT2 : 2 ≤ T (enc a).length := (le_max_right _ _).trans (hTn _)
    have hnT : (enc a).length ≤ T (enc a).length := (le_max_left _ _).trans (hTn _)
  · -- time
    set Q := T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))
    have hE := Nat.mul_succ_div_sqrt_log_two_le_of_le A c₁ c₂ hT2 (hgates (enc a).length)
    have hY := Nat.add_one_pow_le_two_pow_div_sqrt_log_two e hT2 hnT
    have hZ : 2 ^ (A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
        ((enc a).length + 1) ^ e ≤ 2 ^ D₀ * 2 ^ (C₀ * Q) := by
      calc _ ≤ 2 ^ (2 * A * (c₁ + c₂ + 2) * Q + D₀) * 2 ^ (2 * e * Q) :=
            Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hE) hY
        _ = 2 ^ D₀ * 2 ^ (C₀ * Q) := by
            rw [← pow_add, ← pow_add]
            congr 1
            simp only [C₀]
            ring
    have hCQ : C₀ * Q ≤ C₀ * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length)) :=
      Nat.mul_div_le_mul_div_assoc _ _ _
    have hfinal := Nat.mul_two_pow_div_sqrt_log_two_add_le (a := K * 2 ^ D₀) (b := K) (C := C₀)
      hT2
    calc K * (2 ^ (A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
          ((enc a).length + 1) ^ e + 1)
        ≤ K * (2 ^ D₀ * 2 ^ (C₀ * T (enc a).length /
            Nat.sqrt (Nat.log 2 (T (enc a).length))) + 1) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right (hZ.trans (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by norm_num) hCQ))) _)
      _ = K * 2 ^ D₀ * 2 ^ (C₀ * T (enc a).length /
            Nat.sqrt (Nat.log 2 (T (enc a).length))) + K := by ring
      _ ≤ _ := hfinal
  · -- space
    have hpow : ((enc a).length + 1) ^ e ≤ (T (enc a).length + 1) ^ e :=
      Nat.pow_le_pow_left (by omega) e
    have := Nat.mul_add_one_pow_add_le_pow (a := K) (b := K) (d := e) hT2
    calc K * (((enc a).length + 1) ^ e + 1) ≤ K * (T (enc a).length + 1) ^ e + K := by
          rw [Nat.mul_add, Nat.mul_one]
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hpow) _
      _ ≤ _ := this

/-- A problem decided within time `2 ^ (C T / √⌊log₂ T⌋)` lies in the union of these classes. -/
private theorem mem_iUnion_DTIME {L : Set α}
    (h : ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d)) :
    L ∈ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) := by
  obtain ⟨C, d, h⟩ := h
  exact Set.mem_iUnion.mpr ⟨C, 1, 0, fun n => T n ^ d,
    ComputableInTimeAndSpace.mono h (fun a => by rw [Nat.one_mul, Nat.add_zero]) fun _ => le_rfl⟩

/-- **The bounded-error rule**: when `g / g'` is at least `2 / 3` on members and at most `1 / 3`
otherwise, for `g' > 0`, membership is `g' < 2 g`. -/
private theorem iff_lt_two_mul {L : Set α} {a : α} {g g' : ℕ} (hg' : 0 < g')
    (h₁ : a ∈ L → (2 : ℝ) / 3 ≤ g / g') (h₂ : a ∉ L → (g : ℝ) / g' ≤ 1 / 3) :
    a ∈ L ↔ decide (g' < 2 * g) = true := by
  have hpos : (0 : ℝ) < g' := by exact_mod_cast hg'
  rw [decide_eq_true_iff]
  by_cases ha : a ∈ L
  · have := h₁ ha
    rw [le_div_iff₀ hpos] at this
    have : 2 * g' ≤ 3 * g := by exact_mod_cast (by linarith : (2 : ℝ) * g' ≤ 3 * g)
    exact ⟨fun _ => by omega, fun _ => ha⟩
  · have := h₂ ha
    rw [div_le_iff₀ hpos] at this
    have : 3 * g ≤ g' := by exact_mod_cast (by linarith : (3 : ℝ) * g ≤ g')
    exact ⟨fun h => absurd h ha, fun h => by omega⟩

/-- **Bounded-error quantum time `T` in time `2 ^ O(T / √log T)` and space `T ^ O(1)`.** For `T`
with `max n 2 ≤ T n`, every problem in `BQTIME[T]` is decided by one deterministic machine within
time `2 ^ (C T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`: the machine computes the acceptance gap
`g` of the circuit and the projected gap `2 ^ h` of no condition by tensor contraction and accepts
when `2 ^ h < 2 g`. -/
theorem exists_decidableInTimeAndSpace_of_mem_BQTIME (hTn : ∀ n, max n 2 ≤ T n) {L : Set α}
    (hL : L ∈ BQTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨F, c₁, c₂, hgates, hF⟩ := hL
  refine exists_decidableInTimeAndSpace_of_onesProb hTn hgates [0] []
    (rule := fun p => decide (p.2 < 2 * p.1)) (by fun_prop) fun a g g' r h h' => ?_
  rw [UniformCircuitFamily.onesProb, onesProb_nil] at h'
  have hg' : (g' : ℝ) = 2 ^ r := by
    rw [eq_div_iff (by positivity), one_mul] at h'
    exact h'.symm
  have hp : F.acceptProb (enc a) = g / g' := by rw [hg']; exact h
  exact iff_lt_two_mul (by exact_mod_cast hg' ▸ (by positivity : (0 : ℝ) < 2 ^ r))
    (fun ha => hp ▸ (hF a).1 ha) fun ha => hp ▸ (hF a).2 ha

/-- **`BQTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for `T` with `max n 2 ≤ T n`. -/
theorem BQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hTn : ∀ n, max n 2 ≤ T n) :
    BQTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  fun _ hL => mem_iUnion_DTIME (exists_decidableInTimeAndSpace_of_mem_BQTIME hTn hL)

/-- **Nondeterministic quantum time `T` in time `2 ^ O(T / √log T)` and space `T ^ O(1)`.** For
`T` with `max n 2 ≤ T n`, every problem in `NQTIME[T]` is decided by one deterministic machine
within time `2 ^ (C T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`: the machine computes the
acceptance gap of the circuit by tensor contraction and accepts when it is positive. -/
theorem exists_decidableInTimeAndSpace_of_mem_NQTIME (hTn : ∀ n, max n 2 ≤ T n) {L : Set α}
    (hL : L ∈ NQTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨F, c₁, c₂, hgates, hF⟩ := hL
  refine exists_decidableInTimeAndSpace_of_onesProb hTn hgates [0] []
    (rule := fun p => decide (0 < p.1)) (by fun_prop) fun a g g' r h _ => ?_
  rw [hF a, decide_eq_true_iff, UniformCircuitFamily.acceptProb_eq_onesProb, h]
  constructor
  · intro hpos
    exact_mod_cast (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ r)).mp hpos
  · intro hg
    exact div_pos (by exact_mod_cast hg) (by positivity)

/-- **`NQTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for `T` with `max n 2 ≤ T n`. -/
theorem NQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hTn : ∀ n, max n 2 ≤ T n) :
    NQTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  fun _ hL => mem_iUnion_DTIME (exists_decidableInTimeAndSpace_of_mem_NQTIME hTn hL)

/-- **Exact quantum time `T` in time `2 ^ O(T / √log T)`**: exact quantum time lies in
nondeterministic quantum time (`Cslib.Complexity.EQTIME_subset_NQTIME`). -/
theorem EQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hTn : ∀ n, max n 2 ≤ T n) :
    EQTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  (EQTIME_subset_NQTIME T).trans (NQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two hTn)

/-- **Postselected bounded-error quantum time `T` in time `2 ^ O(T / √log T)` and space
`T ^ O(1)`.** For `T` with `max n 2 ≤ T n`, every problem in `PostBQTIME[T]` is decided by one
deterministic machine within time `2 ^ (C T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`: the
machine computes the projected gaps `g` of qubits `0` and `1` and `g'` of qubit `1` by tensor
contraction and accepts when `g' < 2 g`, that is, when the postselected acceptance probability
exceeds `1 / 2`. -/
theorem exists_decidableInTimeAndSpace_of_mem_PostBQTIME (hTn : ∀ n, max n 2 ≤ T n) {L : Set α}
    (hL : L ∈ PostBQTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨F, c₁, c₂, hgates, hF⟩ := hL
  refine exists_decidableInTimeAndSpace_of_onesProb hTn hgates [0, 1] [1]
    (rule := fun p => decide (p.2 < 2 * p.1)) (by fun_prop) fun a g g' r h h' => ?_
  obtain ⟨hpost, h₁, h₂⟩ := hF a
  have hr : (0 : ℝ) < 2 ^ r := by positivity
  have hg' : 0 < g' := by
    rw [h'] at hpost
    exact_mod_cast (div_pos_iff_of_pos_right hr).mp hpost
  have hp : F.postselectedAcceptProb (enc a) = g / g' := by
    rw [UniformCircuitFamily.postselectedAcceptProb, h, h', div_div_div_cancel_right₀ hr.ne']
  exact iff_lt_two_mul hg' (fun ha => hp ▸ h₁ ha) fun ha => hp ▸ h₂ ha

/-- **`PostBQTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for `T` with `max n 2 ≤ T n`. -/
theorem PostBQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hTn : ∀ n, max n 2 ≤ T n) :
    PostBQTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  fun _ hL => mem_iUnion_DTIME (exists_decidableInTimeAndSpace_of_mem_PostBQTIME hTn hL)

end Cslib.Complexity.QuantumContraction
