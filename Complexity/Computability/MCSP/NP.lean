/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding.Certificate
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.MCSP.Basic
public import Complexity.Foundations.Data.BitString.Enumeration
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.BitString.Binary
import Mathlib.Data.List.GetD

/-!
# MCSP is in NP

An instance of the Minimum Circuit Size Problem (`Cslib.MCSP`) is encoded by the `2 ^ n` bits of
its truth table followed by the threshold in binary (`Cslib.MCSP.encInstance`); the length of
the table determines `n`. The problem is in `NP` for this encoding (`Cslib.MCSP.mem_NP`)
[Kabanets and Cai][KabanetsCai2000]: a certificate is a circuit with at most as many gates as the
threshold, in the format of `Cslib.Circuits.Boolean.readCertificate`, and the verifier checks that
it is a circuit and evaluates it on all `2 ^ n` inputs. The threshold may be exponentially larger
than the table; certificates are capped at the truth-table bound `2 ^ n (2 n + 3) + 1`, which
every function on `n` inputs meets (`Cslib.Circuits.Boolean.complexity_le_two_pow_mul_add_one`),
so they stay polynomially long in the length of the table.

## Main definitions

* `Cslib.MCSP.encInstance`: the encoding of instances.
* `Cslib.MCSP.tableFunction`: the Boolean function read from a truth-table list.
* `Cslib.MCSP.verifier`: the verifier.
* `Cslib.MCSP.tableVerifier`: the verifier on the bits of a truth table and a threshold.

## Main results

* `Cslib.MCSP.mem_of_verifier_eq_true`, `Cslib.MCSP.exists_verifier_append`: the verifier accepts
  some certificate exactly for the instances in MCSP, certificates of a fixed length suffice, and
  bits after them are ignored.
* `Cslib.MCSP.complexity_le_of_tableVerifier`, `Cslib.MCSP.exists_tableVerifier_append`: soundness
  and completeness of `tableVerifier` on truth-table lists of length `2 ^ m`.
* `Cslib.MCSP.isVerifier`: the verifier is correct.
* `Cslib.MCSP.computableInPolyTime_verifier`,
  `Cslib.MCSP.computableInPolyTime_tableVerifier`: the verifiers are polynomial-time.
* `Cslib.MCSP.mem_NP`: MCSP is in `NP`.

## References

* [V. Kabanets, J.-Y. Cai, *Circuit minimization problem*][KabanetsCai2000]
-/

@[expose] public section

namespace Cslib.MCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM Complexity

/-- Instances of MCSP encoded by the bits of the truth table, then the threshold in binary. -/
def encInstance : Instance ↪ List Bool :=
  ⟨fun x => encPair encBits encNat (List.ofFn x.table, x.threshold), by
    rintro ⟨n, T, s⟩ ⟨n', T', s'⟩ h
    obtain ⟨hT, hs⟩ := Prod.ext_iff.1 ((encPair encBits encNat).injective h)
    obtain rfl : n = n' := Nat.pow_right_injective le_rfl (by simpa using congrArg List.length hT)
    obtain rfl := List.ofFn_injective hT
    obtain rfl : s = s' := hs
    rfl⟩

theorem encInstance_apply (x : Instance) :
    encInstance x = encPair encBits encNat (List.ofFn x.table, x.threshold) :=
  rfl

/-- The table of an instance is no longer than its encoding. -/
private theorem two_pow_le_length_encInstance (x : Instance) :
    2 ^ x.arity ≤ (encInstance x).length := by
  rw [encInstance_apply, length_encPair, encBits_apply, List.length_ofFn]
  omega

/-- The number of gates a certificate may describe: the threshold, capped at the truth-table bound
that every function meets. -/
def budget (n s : ℕ) : ℕ := min s (2 ^ n * (2 * n + 3) + 1)

/-- The value of the function of an instance at the input with bits `y`. -/
def tableValue (table y : List Bool) : Bool :=
  table.getD (BitString.boundedBinaryValue table.length y.reverse) false

/-- The function on `m` inputs with the truth table `T`, read as MCSP reads truth tables. -/
def tableFunction (m : ℕ) (T : List Bool) : BooleanFunction m :=
  fun y => tableValue T (List.ofFn y)

/-- The verifier for MCSP: the certificate must describe a circuit on `n` inputs with at most
`budget n s` gates (`readCertificate`) that agrees with the truth table on all `2 ^ n` inputs. -/
def verifier (p : Instance × List Bool) : Bool :=
  let c := readCertificate p.1.arity (budget p.1.arity p.1.threshold) p.2
  (codeCheck p.1.arity c.1 && decide (c.2 < p.1.arity + c.1.length)) &&
    (BitString.enumList p.1.arity).all fun y => evalOutput y c.1 c.2 == tableValue
      (List.ofFn p.1.table) y

/-! ### Correctness -/

/-- The verifier reads the function of an instance from its truth table. -/
theorem tableValue_ofFn (x : Instance) (y : BitString x.arity) :
    tableValue (List.ofFn x.table) (List.ofFn y) = x.function y := by
  have hlt := (BitString.equivFin x.arity y).isLt
  rw [tableValue, BitString.boundedBinaryValue_eq, BitString.binaryValue_reverse_ofFn,
    List.length_ofFn, Nat.min_eq_right hlt.le, List.getD_eq_getElem _ _ (by simp),
    List.getElem_ofFn]
  rfl

/-- The truth table of a function, as a list, is read back as the function. -/
@[simp] theorem tableFunction_ofFn_truthTable (m : ℕ) (f : BooleanFunction m) :
    tableFunction m (List.ofFn (truthTable m f)) = f := by
  funext y
  exact (tableValue_ofFn ⟨m, truthTable m f, 0⟩ y).trans (by simp [Instance.function])

/-- The polynomial bounding the length of certificates. -/
noncomputable def certPolynomial : Polynomial ℕ := 40 * (Polynomial.X + 1) ^ 4

private theorem certLength_le (x : Instance) :
    certLength x.arity (budget x.arity x.threshold) ≤
      certPolynomial.eval (encInstance x).length := by
  set L := (encInstance x).length
  have hT := two_pow_le_length_encInstance x
  have hn : x.arity ≤ L := (Nat.lt_two_pow_self).le.trans hT
  have hS : budget x.arity x.threshold ≤ L * (2 * L + 3) + 1 :=
    (Nat.min_le_right _ _).trans (Nat.add_le_add_right
      (Nat.mul_le_mul hT (by omega)) 1)
  simp only [certPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, certLength]
  nlinarith

/-- **Soundness of the verifier.** An instance with an accepted certificate, of any length, is
in MCSP. -/
theorem mem_of_verifier_eq_true {x : Instance} {w : List Bool} (hw : verifier (x, w) = true) :
    x ∈ MCSP := by
  set S := budget x.arity x.threshold with hSdef
  set r := readCertificate x.arity S w
  simp only [verifier, ← hSdef, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, codeCheck_eq_true_iff] at hw
  obtain ⟨⟨hcode, hout⟩, hall⟩ := hw
  have hsome : (Circuit.ofCode x.arity 1 (r.1, [r.2]) : Option (Circuit signature _ 1)).isSome :=
    Circuit.isSome_ofCode_iff.2 ⟨hcode, rfl, by simpa using hout⟩
  set c : Circuit signature x.arity 1 := (Circuit.ofCode x.arity 1 (r.1, [r.2])).get hsome
  have hc : c.code = (r.1, [r.2]) := Circuit.code_of_ofCode_eq_some (Option.some_get _).symm
  have houtput : (c.outputs 0).toNat = r.2 := by
    have := congrArg (fun p => p.2.headD 0) hc
    simpa [Circuit.code] using this
  refine complexity_le_iff.2 ⟨c, Circuit.computes_single_iff.2 fun y => ?_, ?_⟩
  · rw [Circuit.eval_eq_evalOutput, houtput, show c.code.1 = r.1 by rw [hc],
      hall _ (BitString.mem_enumList.2 List.length_ofFn), tableValue_ofFn]
  · calc c.size = r.1.length := by rw [← Circuit.length_code_fst, hc]
      _ ≤ S := length_readCertificate_le _ _ _
      _ ≤ x.threshold := Nat.min_le_left _ _

/-- **Completeness of the verifier.** Every instance in MCSP has a certificate of length
`certLength x.arity (budget x.arity x.threshold)` that is accepted whatever bits follow it. -/
theorem exists_verifier_append {x : Instance} (hx : x ∈ MCSP) :
    ∃ u : List Bool, u.length = certLength x.arity (budget x.arity x.threshold) ∧
      ∀ extra, verifier (x, u ++ extra) = true := by
  set S := budget x.arity x.threshold with hSdef
  have hS : complexity interpretation (single x.function) ≤ S :=
    le_min hx (complexity_le_two_pow_mul_add_one _)
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation)
    (f := single x.function)
  have hcS : c.size ≤ S := hsize ▸ hS
  have hcode : Program.IsCodeFrom signature x.arity 0 c.code.1 := by
    rw [← Program.isSome_ofCode_iff, Circuit.code, Program.ofCode_code]
    rfl
  refine ⟨certificate x.arity S c.code.1 (c.outputs 0).toNat, length_certificate_code c hcS,
    fun extra => ?_⟩
  simp only [verifier, ← hSdef, readCertificate_certificate_code_append c hcS,
    Bool.and_eq_true, codeCheck_eq_true_iff.2 hcode, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, true_and]
  refine ⟨by rw [Circuit.length_code_fst]; exact (c.outputs 0).toNat_lt, fun y hy => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y' : BitString x.arity, List.ofFn y' = y :=
    ⟨fun i => y[i.val]'(by rw [BitString.mem_enumList.1 hy]; exact i.isLt),
      List.ext_getElem (by simp [BitString.mem_enumList.1 hy]) fun _ _ _ => by simp⟩
  rw [← Circuit.eval_eq_evalOutput, Circuit.computes_single_iff.1 hc y, tableValue_ofFn]

/-- `MCSP.verifier` verifies MCSP, with certificates of length `certPolynomial`. -/
theorem isVerifier : IsVerifier encInstance certPolynomial verifier MCSP := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_of_verifier_eq_true hw) fun x hx => ?_
  obtain ⟨u, hu, hV⟩ := exists_verifier_append hx
  exact ⟨u, hu ▸ certLength_le x, fun k => hV _⟩

/-! ### Polynomial time -/

open ComputableTidilyInPolyTime

/-- The verifier on the bits of a truth table, a threshold and a certificate, with the number of
inputs read from the length of the table: `MCSP.verifier` on raw data
(`Cslib.MCSP.verifier_eq_tableVerifier`), defined on every list of bits. -/
def tableVerifier (r : (List Bool × ℕ) × List Bool) : Bool :=
  let n := Nat.log 2 r.1.1.length
  let c := readCertificate n (min r.1.2 (r.1.1.length * (2 * n + 3) + 1)) r.2
  (codeCheck n c.1 && decide (c.2 < n + c.1.length)) &&
    (BitString.enumList n).all fun y => evalOutput y c.1 c.2 == tableValue r.1.1 y

theorem verifier_eq_tableVerifier (p : Instance × List Bool) :
    verifier p = tableVerifier ((List.ofFn p.1.table, p.1.threshold), p.2) := by
  simp only [tableVerifier, List.length_ofFn, Nat.log_pow Nat.one_lt_two]
  rfl

/-- The MCSP instance of a truth table of length `2 ^ m`. -/
private def tableInstance (m s : ℕ) (T : List Bool) (hT : T.length = 2 ^ m) : Instance :=
  ⟨m, fun i => T[i.val]'(by rw [hT]; exact i.isLt), s⟩

private theorem ofFn_tableInstance {m s : ℕ} {T : List Bool} (hT : T.length = 2 ^ m) :
    List.ofFn (tableInstance m s T hT).table = T := by
  change List.ofFn (fun i : Fin (2 ^ m) => T[i.val]'(by rw [hT]; exact i.isLt)) = T
  exact List.ext_getElem (by simp [hT]) fun _ _ _ => by simp

private theorem function_tableInstance {m s : ℕ} {T : List Bool} (hT : T.length = 2 ^ m) :
    (tableInstance m s T hT).function = tableFunction m T := by
  funext y
  rw [← tableValue_ofFn, ofFn_tableInstance hT]
  rfl

/-- An accepted certificate for a truth table of length `2 ^ m` bounds the complexity of its
function. -/
theorem complexity_le_of_tableVerifier {m s : ℕ} {T c : List Bool} (hT : T.length = 2 ^ m)
    (h : tableVerifier ((T, s), c) = true) :
    complexity interpretation (single (tableFunction m T)) ≤ s := by
  have := mem_of_verifier_eq_true (x := tableInstance m s T hT) (w := c)
    (by rw [verifier_eq_tableVerifier, ofFn_tableInstance hT]; exact h)
  rwa [mem_iff, function_tableInstance hT] at this

/-- A truth table of length `2 ^ m` whose function has at most `s` gates has a certificate of
length `certLength m (budget m s)`, accepted whatever bits follow it. -/
theorem exists_tableVerifier_append {m s : ℕ} {T : List Bool} (hT : T.length = 2 ^ m)
    (h : complexity interpretation (single (tableFunction m T)) ≤ s) :
    ∃ u : List Bool, u.length = certLength m (budget m s) ∧
      ∀ extra, tableVerifier ((T, s), u ++ extra) = true := by
  obtain ⟨u, hu, hV⟩ := exists_verifier_append (x := tableInstance m s T hT)
    (by rw [mem_iff, function_tableInstance hT]; exact h)
  refine ⟨u, hu, fun extra => ?_⟩
  rw [← hV extra, verifier_eq_tableVerifier, ofFn_tableInstance hT]
  rfl

/-- The verifier on raw data is polynomial-time. -/
theorem computableInPolyTime_tableVerifier : ComputableInPolyTime tableVerifier
    (encPair (encPair encBits encNat) encBits) encBool := by
  refine .of_tidy ?_
  have hn : ComputableTidilyInPolyTime (fun r : (List Bool × ℕ) × List Bool =>
      Nat.log 2 r.1.1.length) (encPair (encPair encBits encNat) encBits) encUnary :=
    unary_log_two.comp (by fun_prop)
  have hB : ComputableTidilyInPolyTime (fun r : (List Bool × ℕ) × List Bool =>
      r.1.1.length * (2 * Nat.log 2 r.1.1.length + 3) + 1)
      (encPair (encPair encBits encNat) encBits) encUnary := by
    fun_prop
  have hB' := unary_to_binary.comp hB
  simp only [Function.comp_def] at hB'
  have hS : ComputableTidilyInPolyTime (fun r : (List Bool × ℕ) × List Bool =>
      min r.1.2 (r.1.1.length * (2 * Nat.log 2 r.1.1.length + 3) + 1))
      (encPair (encPair encBits encNat) encBits) encUnary := by
    refine binary_to_unary_bounded ?_ hB fun _ => Nat.min_le_right _ _
    simpa only [Nat.min_def] using ite_decide (binary_le' (by fun_prop) hB') (by fun_prop) hB'
  have hc := (computableInPolyTime_readCertificate (.of_tidy hn) (.of_tidy hS) (.of_tidy (snd _
    _))).tidy
  have henum : ComputableTidilyInPolyTime (fun r : (List Bool × ℕ) × List Bool =>
      BitString.enumList (Nat.log 2 r.1.1.length))
      (encPair (encPair encBits encNat) encBits) (encList encBits) := by
    refine bitsEnumList hn (size := fun L => L * L) (by fun_prop) fun r => ?_
    set T := r.1.1.length
    have hT : 2 * T + 1 ≤ (encPair (encPair encBits encNat) encBits r).length := by
      simp only [length_encPair, encBits_apply, T]
      omega
    have hpow : 2 ^ Nat.log 2 T ≤ T + 1 := by
      rcases Nat.eq_zero_or_pos T with h | h
      · simp [h]
      · exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.le_succ T)
    have hlog : 2 * Nat.log 2 T + 1 ≤ 2 * T + 1 := by
      have := Nat.log_le_self 2 T
      omega
    calc 2 ^ Nat.log 2 T * (2 * Nat.log 2 T + 1) ≤ (T + 1) * (2 * T + 1) :=
          Nat.mul_le_mul hpow hlog
      _ ≤ _ := Nat.mul_le_mul (by omega) hT
  have htest : ComputableTidilyInPolyTime
      (fun p : ((List Bool × ℕ) × List Bool) × List Bool =>
        evalOutput p.2 (readCertificate (Nat.log 2 p.1.1.1.length)
          (min p.1.1.2 (p.1.1.1.length * (2 * Nat.log 2 p.1.1.1.length + 3) + 1)) p.1.2).1
          (readCertificate (Nat.log 2 p.1.1.1.length)
          (min p.1.1.2 (p.1.1.1.length * (2 * Nat.log 2 p.1.1.1.length + 3) + 1)) p.1.2).2 ==
        tableValue p.1.1.1 p.2)
      (encPair (encPair (encPair encBits encNat) encBits) encBits) encBool := by
    have hvalue : ComputableTidilyInPolyTime
        (fun p : ((List Bool × ℕ) × List Bool) × List Bool => tableValue p.1.1.1 p.2)
        (encPair (encPair (encPair encBits encNat) encBits) encBits) encBool := by
      have htable : ComputableTidilyInPolyTime
          (fun p : ((List Bool × ℕ) × List Bool) × List Bool => p.1.1.1)
          (encPair (encPair (encPair encBits encNat) encBits) encBits) encBits :=
        (fst _ _).fst'.fst'
      unfold tableValue
      exact bitsGetDWithInput htable (bitsBoundedBinaryValueWithInput (length_bits.comp htable)
        (bitsReverse.comp (snd _ _))) false
    exact beq (computableInPolyTime_evalOutput (.of_tidy (snd _ _)) (.of_tidy (hc.comp (fst _
      _)).fst')
      (.of_tidy (hc.comp (fst _ _)).snd')).tidy hvalue
  unfold tableVerifier
  exact bool_and' (bool_and' (computableInPolyTime_codeCheck (.of_tidy hn) (.of_tidy hc.fst')).tidy
    (binary_lt' hc.snd' (unary_to_binary.comp (unary_add.comp
      (hn.prod ((length_list encGate).comp hc.fst')))))) (allWithInput henum htest)

/-- The MCSP verifier is polynomial-time, on certificates of arbitrary length. -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encInstance encBits) encBool := by
  have hraw : ComputableInPolyTime
      (fun p : Instance × List Bool => ((List.ofFn p.1.table, p.1.threshold), p.2))
      (encPair encInstance encBits) (encPair (encPair encBits encNat) encBits) :=
    .of_eq fun _ => rfl
  rw [funext verifier_eq_tableVerifier]
  exact computableInPolyTime_tableVerifier.comp hraw

/-- **MCSP is in `NP`**, for instances encoded by their truth table and the threshold in
binary. -/
theorem mem_NP : MCSP ∈ NP encInstance :=
  ⟨certPolynomial, verifier, computableInPolyTime_verifier, isVerifier⟩

end Cslib.MCSP
