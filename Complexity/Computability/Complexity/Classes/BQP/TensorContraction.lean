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
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Foundations.Data.Nat.SqrtLog

/-!
# Quantum circuits by tensor contraction: `BQTIME[T] ⊆ DTIME[2 ^ O(T / √log T)]`

The acceptance probability of a circuit of `L` gates over the Hadamard, NOT, CNOT and Toffoli gates
is `acceptGap / 2 ^ h`, where `h` is the number of Hadamard gates
(`Cslib.Quantum.acceptProb_eq_acceptGap`). The acceptance gap is the contraction of the network of
the circuit and its mirror copy (`Cslib.Quantum.PathNetwork.contraction_network`), and over `ℕ`,
with the Hadamard sign `2 ^ (h + 1) - 1`, its residue modulo `2 ^ (h + 1)`
(`Cslib.Quantum.PathNetwork.contraction_network_mod`). The network has `s = 4 N` edges for
`N ≤ 3 L` occurrences of qubits in gates, degree at most six and a bipartition, so it is admissible
for the contraction algorithm of Theorem D.1 of [OpenAI2026ETH]
(`CountingSimulation.fastContractionAlgorithm`) at size `s`, which contracts it in time
`2 ^ O(s / √⌊log₂ s⌋)` times a polynomial and in polynomial space. The width of the circuit does
not enter the exponent: qubits that no gate touches cost nothing.

So the acceptance gap of polynomial-time computed circuits is computed by one machine in time
`2 ^ (A (L + 1) / √⌊log₂ (L + 2)⌋)` times a polynomial in the input length, and in polynomial space
(`QuantumContraction.exists_computableInO_gapValue`). For a uniform family with `O(T)` gates this
decides the problem of the family: `BQTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]` for
`max n 2 ≤ T n`, with a joint polynomial space bound `T ^ d`
(`QuantumContraction.BQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
`QuantumContraction.exists_decidableInTimeAndSpace_of_mem_BQTIME`). No time-constructibility of
`T` is needed, since the machine never computes `T`. The novelty of this bound has not been
checked against the literature.

## Main definitions

* `Cslib.Complexity.QuantumContraction.gapValue`: the acceptance gap as the simulator computes
  it.

## Main results

* `Cslib.Quantum.PathNetwork.explicitAdmissible_network`: the network is admissible.
* `Cslib.Complexity.QuantumContraction.gapValue_eq`: the simulator computes the acceptance gap.
* `Cslib.Complexity.QuantumContraction.exists_computableInO_rule`,
  `Cslib.Complexity.QuantumContraction.exists_computableInO_gapValue`: the simulator and its
  resources.
* `Cslib.Complexity.QuantumContraction.exists_decidableInTimeAndSpace_of_mem_BQTIME`,
  `Cslib.Complexity.QuantumContraction.BQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`: the
  class containments.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
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
nonempty list of well-formed gate codes. -/
theorem explicitAdmissible_network (neg : ℕ) (X : List Bool) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) (hne : gs ≠ []) :
    ExplicitAdmissible 6 (4 * (occurrences gs).length) (network neg X gs) := by
  have h3 : ∀ g ∈ gs, (qubits g).length ≤ 3 := fun g hg => length_qubits_le_three (hgs g hg)
  have hL : 1 ≤ gs.length := List.length_pos_iff.mpr hne
  have hLN := length_le_length_occurrences gs
  have hlog : 1 ≤ Nat.log 2 (4 * (occurrences gs).length) := Nat.log_pos (by norm_num) (by omega)
  refine ⟨isRowsFirstBipartite_network neg X fun g hg => nodup_qubits (hgs g hg), ?_, ?_, ?_,
    length_table_network neg X h3, ?_⟩
  · rw [numEdges_network]
    omega
  · exact (maxDegree_network_le neg X h3).trans (by omega)
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
network with Hadamard sign `2 ^ (h + 1) - 1` on the input register `X`. -/
@[expose] def contractionInput (gs : List GateCode) (X : List Bool) :
    ℕ × ℕ × ExplicitTensorNetwork ℕ :=
  (hadamardCount gs + 1, network (2 ^ (hadamardCount gs + 1) - 1 : ℕ) X gs)

/-- The answer for a circuit without gates: the bit of qubit `0`. -/
@[expose] def fallback (X : List Bool) : ℕ := if X.getD 0 false then 1 else 0

/-- **The acceptance gap as the simulator computes it**: the residue of the contraction of the
network modulo `2 ^ (h + 1)`, or the bit of qubit `0` for a circuit without gates. -/
@[expose] def gapValue (gs : List GateCode) (X : List Bool) : ℕ :=
  if guard gs then (contractionInput gs X).2.2.contraction % 2 ^ (contractionInput gs X).1
  else fallback X

private theorem acceptGap_nil (X : List Bool) :
    acceptGap [] X = if X.headD false then 1 else 0 := by
  simp only [acceptGap, hadamardCount_nil, acceptTerm,
    pathRun, List.ofFn_zero, List.foldl_nil, true_and, Bool.xor_self, Bool.false_eq_true,
    ↓reduceIte]
  cases X.headD false <;> rfl

/-- **The simulator computes the acceptance gap** of well-formed gate codes on a nonempty input
register. -/
theorem gapValue_eq {X : List Bool} (hX : 0 < X.length) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) : gapValue gs X = (acceptGap gs X).toNat := by
  unfold gapValue
  split
  · exact contraction_network_mod X hX gs hgs (Nat.lt_succ_self _)
  · next hg =>
    obtain rfl : gs = [] := by simpa [guard] using hg
    rw [acceptGap_nil, fallback]
    cases X with
    | nil => rfl
    | cons b X => cases b <;> rfl

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

/-- **The simulator with polynomial-time postprocessing.** For polynomial-time computed gate codes
`gs a`, well formed on the polynomial-time computed register `X a`, one machine computes
`rule (h, gapValue (gs a) (X a))`, for `h` the number of Hadamard gates and a polynomial-time
`rule`, in time `2 ^ (A (L + 1) / √⌊log₂ (L + 2)⌋)` times a polynomial in the input length and in
polynomial space, where `L` is the number of gates. -/
theorem exists_computableInO_rule (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits) (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length)
    {β : Type} {encβ : β ↪ List Bool} {rule : ℕ × ℕ → β}
    (hrule : ComputableInPolyTime rule (encPair encUnary encNat) encβ) :
    ∃ A e : ℕ, ComputableInO (fun a => rule (hadamardCount (gs a), gapValue (gs a) (X a))) enc
      encβ
      (fun a => 2 ^ (A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
        ((enc a).length + 1) ^ e)
      (fun a => ((enc a).length + 1) ^ e) := by
  obtain ⟨K, hK⟩ := fastContractionAlgorithm.bound 6 1
  -- the polynomial-time parts
  have hh : ComputableInPolyTime (fun a => hadamardCount (gs a)) enc encUnary := by
    simp only [hadamardCount_eq_countP]
    fun_prop
  have hguard : ComputableInPolyTime (fun a => guard (gs a)) enc encBool := by
    unfold guard
    fun_prop
  have hinput : ComputableInPolyTime (fun a => contractionInput (gs a) (X a)) enc
      (encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)) :=
    (unary_to_binary.comp (unary_add' hh (const 1))).prod (computableInPolyTime_network
      (binary_sub' (binary_pow' (const 2) (unary_add' hh (const 1)))
        (const 1)) hX hgs)
  have hfb : ComputableInPolyTime (fun a => fallback (X a)) enc encNat :=
    ite_decide (decide_eq' (bitsGetDWithInput hX (const 0) false) (const true)) (const 1) (const 0)
  -- the machine
  let cv : NativeCertificate (fun a => gapValue (gs a) (X a)) enc encNat :=
    (NativeCertificate.branch (NativeCertificate.ofPolyTime hguard)
      (fastContractionAlgorithm.certificate.comp (NativeCertificate.ofPolyTime hinput))
      (NativeCertificate.ofPolyTime hfb)).congr fun _ => rfl
  let cpair := (NativeCertificate.ofPolyTime hh).prod cv
  let ctotal := (NativeCertificate.ofPolyTime hrule).comp cpair
  -- polynomial bounds
  have hpg := NativeCertificate.ofPolyTime_isPolynomial hguard
  have hpi := NativeCertificate.ofPolyTime_isPolynomial hinput
  have hpf := NativeCertificate.ofPolyTime_isPolynomial hfb
  have hph := NativeCertificate.ofPolyTime_isPolynomial hh
  have hpr := NativeCertificate.ofPolyTime_isPolynomial hrule
  obtain ⟨cg, dg, htg⟩ := hpg.1.exists_le
  obtain ⟨cg', dg', hsg⟩ := hpg.2.exists_le
  obtain ⟨ci, di, hti⟩ := hpi.1.exists_le
  obtain ⟨ci', di', hsi⟩ := hpi.2.exists_le
  obtain ⟨cf, df, htf⟩ := hpf.1.exists_le
  obtain ⟨cf', df', hsf⟩ := hpf.2.exists_le
  obtain ⟨ch, dh, hth⟩ := hph.1.exists_le
  obtain ⟨ch', dh', hsh⟩ := hph.2.exists_le
  obtain ⟨cr, dr, htr⟩ := hpr.1.exists_le
  obtain ⟨cr', dr', hsr⟩ := hpr.2.exists_le
  obtain ⟨p, q, hlen⟩ := hinput.polyBounded_length.exists_le
  -- the contraction on guarded inputs
  have hfast (a : α) (hga : guard (gs a) = true) :
      fastContractionAlgorithm.certificate.time (contractionInput (gs a) (X a)) ≤
          K * (((encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork))
            (contractionInput (gs a) (X a))).length + 1) ^ K *
            2 ^ (12 * K * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) ∧
        fastContractionAlgorithm.certificate.space (contractionInput (gs a) (X a)) ≤
          K * (((encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork))
            (contractionInput (gs a) (X a))).length + 1) ^ K := by
    have hne : gs a ≠ [] := by simpa [guard] using hga
    have hL : 1 ≤ (gs a).length := List.length_pos_iff.mpr hne
    have hLN := length_le_length_occurrences (gs a)
    have hhL : hadamardCount (gs a) ≤ (gs a).length := by
      rw [hadamardCount_eq_countP]
      exact List.countP_le_length
    have hb := hK (4 * (occurrences (gs a)).length) (hadamardCount (gs a) + 1)
      (network (2 ^ (hadamardCount (gs a) + 1) - 1 : ℕ) (X a) (gs a)) (by omega) (by omega)
      (by omega) (explicitAdmissible_network _ (X a) (hwf a) hne)
    exact ⟨hb.1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
      (exponent_le K (hwf a) hne))), hb.2⟩
  -- the space of the pair, and so the length of its output
  set ds := dg' + di' + df' + dh' + q * K
  set CS := cg' + ci' + cf' + ch' + K * (p + 1) ^ K
  have hY {a : α} {d d' : ℕ} (h : d ≤ d') :
      ((enc a).length + 1) ^ d ≤ ((enc a).length + 1) ^ d' :=
    Nat.pow_le_pow_right (Nat.le_add_left 1 _) h
  have hinlen (a : α) : (((encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork))
      (contractionInput (gs a) (X a))).length + 1) ^ K ≤
        (p + 1) ^ K * ((enc a).length + 1) ^ (q * K) := by
    have h1 := hlen a
    have h2 : 1 ≤ ((enc a).length + 1) ^ q := Nat.one_le_pow _ _ (Nat.le_add_left 1 _)
    calc _ ≤ ((p + 1) * ((enc a).length + 1) ^ q) ^ K := Nat.pow_le_pow_left (by nlinarith) K
      _ = _ := by rw [mul_pow, pow_mul]
  have hspace_pair (a : α) : cpair.space a ≤ CS * ((enc a).length + 1) ^ ds := by
    have e1 := (hsh a).trans (Nat.mul_le_mul_left ch' (hY (a := a) (show dh' ≤ ds by omega)))
    have e2 := (hsg a).trans (Nat.mul_le_mul_left cg' (hY (a := a) (show dg' ≤ ds by omega)))
    have e3 := (hsi a).trans (Nat.mul_le_mul_left ci' (hY (a := a) (show di' ≤ ds by omega)))
    have e4 := (hsf a).trans (Nat.mul_le_mul_left cf' (hY (a := a) (show df' ≤ ds by omega)))
    change (NativeCertificate.ofPolyTime hh).space a +
        ((NativeCertificate.ofPolyTime hguard).space a + if guard (gs a) then
          (NativeCertificate.ofPolyTime hinput).space a +
            fastContractionAlgorithm.certificate.space (contractionInput (gs a) (X a))
          else (NativeCertificate.ofPolyTime hfb).space a) ≤ _
    split
    · next hga =>
      have e5 := ((hfast a hga).2.trans (Nat.mul_le_mul_left K (hinlen a))).trans
        (show K * ((p + 1) ^ K * ((enc a).length + 1) ^ (q * K)) ≤
          K * (p + 1) ^ K * ((enc a).length + 1) ^ ds by
            rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hY (by omega)))
      calc _ ≤ ch' * ((enc a).length + 1) ^ ds + (cg' * ((enc a).length + 1) ^ ds +
            (ci' * ((enc a).length + 1) ^ ds + K * (p + 1) ^ K * ((enc a).length + 1) ^ ds)) :=
            Nat.add_le_add e1 (Nat.add_le_add e2 (Nat.add_le_add e3 e5))
        _ = (ch' + cg' + ci' + K * (p + 1) ^ K) * ((enc a).length + 1) ^ ds := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by simp only [CS]; omega)
    · calc _ ≤ ch' * ((enc a).length + 1) ^ ds + (cg' * ((enc a).length + 1) ^ ds +
            cf' * ((enc a).length + 1) ^ ds) := Nat.add_le_add e1 (Nat.add_le_add e2 e4)
        _ = (ch' + cg' + cf') * ((enc a).length + 1) ^ ds := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by simp only [CS]; omega)
  obtain ⟨K₀, -, hK₀⟩ := cpair.computes
  -- the postprocessing
  set CR := K₀ * CS + K₀ + 1
  have hpairlen (a : α) : (encPair encUnary encNat
      (hadamardCount (gs a), gapValue (gs a) (X a))).length + 1 ≤
        CR * ((enc a).length + 1) ^ ds := by
    have h1 := hK₀ a
    have h2 := hspace_pair a
    have h3 : 1 ≤ ((enc a).length + 1) ^ ds := Nat.one_le_pow _ _ (Nat.le_add_left 1 _)
    change _ ≤ K₀ * (cpair.space a + 1) at h1
    simp only [CR]
    nlinarith
  have hrule_time (a : α) : (NativeCertificate.ofPolyTime hrule).time
      (hadamardCount (gs a), gapValue (gs a) (X a)) ≤
        cr * CR ^ dr * ((enc a).length + 1) ^ (ds * dr) := by
    refine (htr _).trans ?_
    calc _ ≤ cr * (CR * ((enc a).length + 1) ^ ds) ^ dr :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hpairlen a) dr)
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hrule_space (a : α) : (NativeCertificate.ofPolyTime hrule).space
      (hadamardCount (gs a), gapValue (gs a) (X a)) ≤
        cr' * CR ^ dr' * ((enc a).length + 1) ^ (ds * dr') := by
    refine (hsr _).trans ?_
    calc _ ≤ cr' * (CR * ((enc a).length + 1) ^ ds) ^ dr' :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hpairlen a) dr')
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  -- the totals
  set e := dg + di + df + dh + q * K + ds * dr + ds * dr' + ds
  set k := cg + ci + cf + ch + K * (p + 1) ^ K + cr * CR ^ dr + CS + cr' * CR ^ dr' + 1
  refine ⟨12 * K, e, ctotal.computes.mono k (fun a => ?_) (fun a => ?_)⟩
  · -- time
    set E := 12 * K * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))
    set Z := 2 ^ E * ((enc a).length + 1) ^ e
    have hZ {d : ℕ} (h : d ≤ e) : ((enc a).length + 1) ^ d ≤ Z :=
      (hY h).trans (Nat.le_mul_of_pos_left _ Nat.one_le_two_pow)
    have e1 := (hth a).trans (Nat.mul_le_mul_left ch (hZ (show dh ≤ e by omega)))
    have e2 := (htg a).trans (Nat.mul_le_mul_left cg (hZ (show dg ≤ e by omega)))
    have e3 := (hti a).trans (Nat.mul_le_mul_left ci (hZ (show di ≤ e by omega)))
    have e4 := (htf a).trans (Nat.mul_le_mul_left cf (hZ (show df ≤ e by omega)))
    have e6 := (hrule_time a).trans (Nat.mul_le_mul_left _ (hZ (show ds * dr ≤ e by omega)))
    change (NativeCertificate.ofPolyTime hh).time a +
        ((NativeCertificate.ofPolyTime hguard).time a + if guard (gs a) then
          (NativeCertificate.ofPolyTime hinput).time a +
            fastContractionAlgorithm.certificate.time (contractionInput (gs a) (X a))
          else (NativeCertificate.ofPolyTime hfb).time a) +
        (NativeCertificate.ofPolyTime hrule).time
          (hadamardCount (gs a), gapValue (gs a) (X a)) ≤ k * (Z + 1)
    have hk : ∀ c, c ≤ k → c * Z ≤ k * (Z + 1) := fun c hc =>
      (Nat.mul_le_mul_right _ hc).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
    split
    · next hga =>
      have e5 : fastContractionAlgorithm.certificate.time (contractionInput (gs a) (X a)) ≤
          K * (p + 1) ^ K * Z := by
        refine (hfast a hga).1.trans ?_
        calc _ ≤ K * ((p + 1) ^ K * ((enc a).length + 1) ^ (q * K)) * 2 ^ E :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hinlen a))
          _ = K * (p + 1) ^ K * (2 ^ E * ((enc a).length + 1) ^ (q * K)) := by ring
          _ ≤ K * (p + 1) ^ K * Z :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hY (by omega)))
      calc _ ≤ ch * Z + (cg * Z + (ci * Z + K * (p + 1) ^ K * Z)) + cr * CR ^ dr * Z :=
            Nat.add_le_add (Nat.add_le_add e1 (Nat.add_le_add e2 (Nat.add_le_add e3 e5))) e6
        _ = (ch + cg + ci + K * (p + 1) ^ K + cr * CR ^ dr) * Z := by ring
        _ ≤ _ := hk _ (by simp only [k]; omega)
    · calc _ ≤ ch * Z + (cg * Z + cf * Z) + cr * CR ^ dr * Z :=
            Nat.add_le_add (Nat.add_le_add e1 (Nat.add_le_add e2 e4)) e6
        _ = (ch + cg + cf + cr * CR ^ dr) * Z := by ring
        _ ≤ _ := hk _ (by simp only [k]; omega)
  · -- space
    have e1 := (hspace_pair a).trans (Nat.mul_le_mul_left CS (hY (a := a) (show ds ≤ e by omega)))
    have e2 := (hrule_space a).trans
      (Nat.mul_le_mul_left _ (hY (a := a) (show ds * dr' ≤ e by omega)))
    change cpair.space a + (NativeCertificate.ofPolyTime hrule).space
      (hadamardCount (gs a), gapValue (gs a) (X a)) ≤ k * (((enc a).length + 1) ^ e + 1)
    calc _ ≤ CS * ((enc a).length + 1) ^ e + cr' * CR ^ dr' * ((enc a).length + 1) ^ e :=
          Nat.add_le_add e1 e2
      _ = (CS + cr' * CR ^ dr') * ((enc a).length + 1) ^ e := by ring
      _ ≤ k * ((enc a).length + 1) ^ e :=
          Nat.mul_le_mul_right _ (by simp only [k]; omega)
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- **The simulator.** For polynomial-time computed gate codes `gs a`, well formed on the
polynomial-time computed register `X a`, one machine computes `gapValue (gs a) (X a)`, the
acceptance gap when `X a` is nonempty (`QuantumContraction.gapValue_eq`), in time
`2 ^ (A (L + 1) / √⌊log₂ (L + 2)⌋)` times a polynomial in the input length and in polynomial
space, where `L` is the number of gates. -/
theorem exists_computableInO_gapValue (hgs : ComputableInPolyTime gs enc (encList encGateCode))
    (hX : ComputableInPolyTime X enc encBits)
    (hwf : ∀ a, ∀ g ∈ gs a, g.WellFormed (X a).length) :
    ∃ A e : ℕ, ComputableInO (fun a => gapValue (gs a) (X a)) enc encNat
      (fun a => 2 ^ (A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
        ((enc a).length + 1) ^ e)
      (fun a => ((enc a).length + 1) ^ e) :=
  exists_computableInO_rule hgs hX hwf (rule := Prod.snd) (snd _ _)

end Machine

/-- **The acceptance probability from the simulator**: for well-formed codes on `m > 0` qubits and
an input `x` of length at most `m`, the acceptance probability is `gapValue / 2 ^ h` on the padded
register. -/
theorem acceptProb_eq_gapValue {m : ℕ} (hm : 0 < m) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, g.WellFormed m) {x : List Bool} (hx : x.length ≤ m) :
    acceptProb m gs x =
      (gapValue gs (x ++ List.replicate (m - x.length) false) : ℝ) / 2 ^ hadamardCount gs := by
  have hlen : (x ++ List.replicate (m - x.length) false).length = m := by simp; omega
  have hgs' : ∀ g ∈ gs, g.WellFormed (x ++ List.replicate (m - x.length) false).length := by
    rw [hlen]
    exact hgs
  have hm' : 0 < (x ++ List.replicate (m - x.length) false).length := by
    rw [hlen]
    exact hm
  rw [acceptProb_eq_acceptGap hm gs hgs x, ofFn_inputState hx, gapValue_eq hm' hgs']
  congr 1
  have := Int.toNat_of_nonneg (acceptGap_nonneg_and_le hm' gs hgs').1
  exact_mod_cast this.symm

/-! ### The class containments -/

/-- The exponent in terms of a bound `c₁ T + c₂` on the number of gates `L`. -/
private theorem exponent_le_of_le (A c₁ c₂ : ℕ) {T L : ℕ} (hT : 2 ≤ T) (hL : L ≤ c₁ * T + c₂) :
    A * (L + 1) / Nat.sqrt (Nat.log 2 (L + 2)) ≤
      2 * A * (c₁ + c₂ + 2) * (T / Nat.sqrt (Nat.log 2 T)) + (2 * A * (c₁ + c₂ + 2) + 3 * A) := by
  have hM : L + 2 ≤ (c₁ + c₂ + 2) * T := by nlinarith
  calc A * (L + 1) / Nat.sqrt (Nat.log 2 (L + 2))
      ≤ A * (L + 2) / Nat.sqrt (Nat.log 2 (L + 2)) :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
    _ ≤ A * ((L + 2) / Nat.sqrt (Nat.log 2 (L + 2))) + A := Nat.mul_div_le_mul_div_add _ _ _
    _ ≤ A * (2 * ((c₁ + c₂ + 2) * T / Nat.sqrt (Nat.log 2 ((c₁ + c₂ + 2) * T))) + 2) + A := by
        gcongr
        exact Nat.div_sqrt_log_two_le_of_le hM
    _ ≤ A * (2 * ((c₁ + c₂ + 2) * (T / Nat.sqrt (Nat.log 2 T)) + (c₁ + c₂ + 2)) + 2) + A := by
        gcongr
        exact Nat.mul_div_sqrt_log_two_le _ T
    _ = _ := by ring

/-- A polynomial in `n + 1 ≤ T + 1` is at most `2 ^ (2 e T / √⌊log₂ T⌋)`. -/
private theorem add_one_pow_le {n T : ℕ} (e : ℕ) (hT : 2 ≤ T) (hn : n ≤ T) :
    (n + 1) ^ e ≤ 2 ^ (2 * e * (T / Nat.sqrt (Nat.log 2 T))) := by
  have h1 := Nat.one_le_div_sqrt_log_two hT
  have h2 := Nat.log_two_le_div_sqrt_log_two T
  calc (n + 1) ^ e ≤ (2 ^ (Nat.log 2 T + 1)) ^ e :=
        Nat.pow_le_pow_left ((Nat.succ_le_succ hn).trans (Nat.lt_pow_succ_log_self one_lt_two T)) e
    _ = 2 ^ (e * (Nat.log 2 T + 1)) := by rw [← pow_mul, mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

variable {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}

/-- **Bounded-error quantum time `T` in time `2 ^ O(T / √log T)` and space `T ^ O(1)`.** For `T`
with `max n 2 ≤ T n`, every problem in `BQTIME[T]` is decided by one deterministic machine within
time `2 ^ (C T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`: the machine computes the acceptance gap
of the circuit by tensor contraction and compares it with half of `2 ^ h`. -/
theorem exists_decidableInTimeAndSpace_of_mem_BQTIME (hTn : ∀ n, max n 2 ≤ T n) {L : Set α}
    (hL : L ∈ BQTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) := by
  obtain ⟨F, c₁, c₂, hgates, hF⟩ := hL
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
  have hrule : ComputableInPolyTime (fun p : ℕ × ℕ => decide (2 ^ p.1 < 2 * p.2))
      (encPair encUnary encNat) encBool := by fun_prop
  obtain ⟨A, e, hc⟩ := exists_computableInO_rule hgs hX hwf hrule
  obtain ⟨K, hK, -⟩ := hc
  -- correctness
  have hcorrect (a : α) : a ∈ L ↔
      decide (2 ^ hadamardCount (gs a) < 2 * gapValue (gs a) (X a)) = true := by
    have hp := acceptProb_eq_gapValue (F.width_pos (enc a).length)
      (F.wellFormed (enc a).length) (F.le_width (enc a).length)
    change F.acceptProb (enc a) = _ at hp
    set g := gapValue (gs a) (X a)
    set r := hadamardCount (gs a)
    have hpos : (0 : ℝ) < 2 ^ r := by positivity
    rw [decide_eq_true_iff]
    by_cases ha : a ∈ L
    · have := (hF a).1 ha
      rw [hp, le_div_iff₀ hpos] at this
      have h1 : (2 : ℝ) * 2 ^ r ≤ 3 * g := by linarith
      have h2 : 2 * 2 ^ r ≤ 3 * g := by exact_mod_cast h1
      have h3 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      exact ⟨fun _ => by omega, fun _ => ha⟩
    · have := (hF a).2 ha
      rw [hp, div_le_iff₀ hpos] at this
      have h1 : (3 : ℝ) * g ≤ 2 ^ r := by linarith
      have h2 : 3 * g ≤ 2 ^ r := by exact_mod_cast h1
      have h3 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      exact ⟨fun h => absurd h ha, fun h => by omega⟩
  -- the bounds
  set C₀ := 2 * A * (c₁ + c₂ + 2) + 2 * e
  set D₀ := 2 * A * (c₁ + c₂ + 2) + 3 * A
  refine ⟨(K * 2 ^ D₀ + K + 1) * (C₀ + 1), K + K + 2 * e,
    decidableInTimeAndSpace_iff.mpr ⟨_, hK.mono (fun a => ?_) (fun a => ?_), hcorrect⟩⟩
  all_goals
    have hT2 : 2 ≤ T (enc a).length := (le_max_right _ _).trans (hTn _)
    have hnT : (enc a).length ≤ T (enc a).length := (le_max_left _ _).trans (hTn _)
  · -- time
    set S := T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))
    have hE := exponent_le_of_le A c₁ c₂ hT2 (hgates (enc a).length)
    have hY := add_one_pow_le e hT2 hnT
    have hZ : 2 ^ (A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
        ((enc a).length + 1) ^ e ≤ 2 ^ D₀ * 2 ^ (C₀ * S) := by
      calc _ ≤ 2 ^ (2 * A * (c₁ + c₂ + 2) * S + D₀) * 2 ^ (2 * e * S) :=
            Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hE) hY
        _ = 2 ^ D₀ * 2 ^ (C₀ * S) := by
            rw [← pow_add, ← pow_add]
            congr 1
            simp only [C₀]
            ring
    have hCS : C₀ * S ≤ C₀ * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length)) :=
      Nat.mul_div_le_mul_div_assoc _ _ _
    have hfinal := Nat.mul_two_pow_div_sqrt_log_two_add_le (a := K * 2 ^ D₀) (b := K) (C := C₀)
      hT2
    calc K * (2 ^ (A * ((gs a).length + 1) / Nat.sqrt (Nat.log 2 ((gs a).length + 2))) *
          ((enc a).length + 1) ^ e + 1)
        ≤ K * (2 ^ D₀ * 2 ^ (C₀ * T (enc a).length /
            Nat.sqrt (Nat.log 2 (T (enc a).length))) + 1) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_right (hZ.trans (Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by norm_num) hCS))) _)
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

/-- **`BQTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for `T` with `max n 2 ≤ T n`. -/
theorem BQTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hTn : ∀ n, max n 2 ≤ T n) :
    BQTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) := by
  intro L hL
  obtain ⟨C, d, h⟩ := exists_decidableInTimeAndSpace_of_mem_BQTIME hTn hL
  exact Set.mem_iUnion.mpr ⟨C, 1, 0, fun n => T n ^ d,
    ComputableInTimeAndSpace.mono h (fun a => by rw [Nat.one_mul, Nat.add_zero]) fun _ => le_rfl⟩

end Cslib.Complexity.QuantumContraction
