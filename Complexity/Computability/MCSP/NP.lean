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
import Complexity.Foundations.Data.BitString.List
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.List.Lookup
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
* `Cslib.MCSP.sampleBudget`, `Cslib.MCSP.budget`: certificate gate budgets for `t` samples and for
  a full `2 ^ n`-entry truth table.
* `Cslib.MCSP.validCertificate`, `Cslib.MCSP.evalCertificate`,
  `Cslib.MCSP.checkCertificateOn`, `Cslib.MCSP.checkCertificate`: certificate well-formedness,
  evaluation, and generic parameterized verifiers over a list of tests and over all `2 ^ m` inputs.
* `Cslib.MCSP.tableFunction`: the Boolean function read from a truth-table list.
* `Cslib.MCSP.verifier`: the verifier.
* `Cslib.MCSP.tableVerifier`: the verifier on the bits of a truth table and a threshold.

## Main results

* `Cslib.MCSP.exists_circuit_of_checkCertificateOn`,
  `Cslib.MCSP.exists_checkCertificateOn_append`,
  `Cslib.MCSP.exists_circuit_of_checkCertificate`,
  `Cslib.MCSP.exists_checkCertificate_append`,
  `Cslib.MCSP.exists_circuit_of_validCertificate`,
  `Cslib.MCSP.exists_validCertificate_of_circuit`: soundness and completeness of the generic
  verifiers and of `validCertificate` / `evalCertificate`.
* `Cslib.MCSP.mem_of_verifier_eq_true`, `Cslib.MCSP.exists_verifier_append`: the verifier accepts
  some certificate exactly for the instances in MCSP, certificates of a fixed length suffice, and
  bits after them are ignored.
* `Cslib.MCSP.complexity_le_of_tableVerifier`, `Cslib.MCSP.exists_tableVerifier_append`: soundness
  and completeness of `tableVerifier` on truth-table lists of length `2 ^ m`.
* `Cslib.MCSP.isVerifier`: the verifier is correct.
* `Cslib.MCSP.computableInPolyTime_tableValue`: truth table lookup is polynomial-time.
* `Cslib.MCSP.computableInPolyTime_validCertificate`,
  `Cslib.MCSP.computableInPolyTime_evalCertificate`,
  `Cslib.MCSP.computableInPolyTime_checkCertificateOn`,
  `Cslib.MCSP.computableInPolyTime_checkCertificate`: certificate well-formedness, evaluation, and
  generic verification are polynomial-time.
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

/-- The number of gates a certificate for `t` samples on `n` inputs may describe: the threshold
`s`, capped at the sample-set bound `t * (2 * n + 3) + 1`. -/
def sampleBudget (n t s : ℕ) : ℕ := min s (t * (2 * n + 3) + 1)

@[simp] theorem sampleBudget_zero (n t : ℕ) : sampleBudget n t 0 = 0 :=
  Nat.min_eq_left (Nat.zero_le _)

/-- The number of gates a certificate may describe: the threshold, capped at the truth-table bound
that every function meets. -/
def budget (n s : ℕ) : ℕ := sampleBudget n (2 ^ n) s

/-- The value of the function of an instance at the input with bits `y`. -/
def tableValue (table y : List Bool) : Bool :=
  table.getD (BitString.boundedBinaryValue table.length y.reverse) false

/-- The function on `m` inputs with the truth table `T`, read as MCSP reads truth tables. -/
def tableFunction (m : ℕ) (T : List Bool) : BooleanFunction m :=
  fun y => tableValue T (List.ofFn y)

/-- Whether `w`, read as a certificate for `m` inputs and gate budget `S`, describes a well-formed
circuit code with a valid output wire. -/
def validCertificate (m S : ℕ) (w : List Bool) : Bool :=
  let c := readCertificate m S w
  codeCheck m c.1 && decide (c.2 < m + c.1.length)

/-- Evaluate the certificate `w` (for `m` inputs and gate budget `S`) on input `y`. -/
def evalCertificate (m S : ℕ) (w y : List Bool) : Bool :=
  let c := readCertificate m S w
  evalOutput y c.1 c.2

/-- A certificate verifier parameterized by a list of tests, the input bitstring of each test, and
the acceptance condition on a test and the circuit output on its input. -/
def checkCertificateOn {α : Type} (tests : List α) (input : α → List Bool)
    (accept : α → Bool → Bool) (m S : ℕ) (w : List Bool) : Bool :=
  validCertificate m S w &&
    tests.all fun t => accept t (evalCertificate m S w (input t))

/-- A certificate verifier on all `2 ^ m` inputs, parameterized by the acceptance condition on an
input and the circuit output on that input. -/
def checkCertificate (accept : List Bool → Bool → Bool) (m S : ℕ) (w : List Bool) : Bool :=
  checkCertificateOn (BitString.enumList m) id accept m S w

/-- An accepted certificate decoded by `checkCertificateOn` describes a circuit of size at most `S`
meeting the acceptance condition on every test in `tests` whose input is `List.ofFn y`. -/
theorem exists_circuit_of_checkCertificateOn {α : Type} {tests : List α}
    {input : α → List Bool} {accept : α → Bool → Bool} {m S : ℕ} {w : List Bool}
    (hw : checkCertificateOn tests input accept m S w = true) :
    ∃ C : Circuit signature m 1, C.size ≤ S ∧
      ∀ t ∈ tests, ∀ y : BitString m, input t = List.ofFn y →
        accept t (C.eval interpretation y 0) = true := by
  set r := readCertificate m S w
  simp only [checkCertificateOn, validCertificate, evalCertificate, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, codeCheck_eq_true_iff] at hw
  obtain ⟨⟨hcode, hout⟩, hall⟩ := hw
  have hsome : (Circuit.ofCode m 1 (r.1, [r.2]) : Option (Circuit signature _ 1)).isSome :=
    Circuit.isSome_ofCode_iff.2 ⟨hcode, rfl, by simpa using hout⟩
  set c : Circuit signature m 1 := (Circuit.ofCode m 1 (r.1, [r.2])).get hsome
  have hc : c.code = (r.1, [r.2]) := Circuit.code_of_ofCode_eq_some (Option.some_get _).symm
  have houtput : (c.outputs 0).toNat = r.2 := by
    have := congrArg (fun p => p.2.headD 0) hc
    simpa [Circuit.code] using this
  refine ⟨c, ?_, fun t ht y hy => ?_⟩
  · calc c.size = r.1.length := by rw [← Circuit.length_code_fst, hc]
      _ ≤ S := length_readCertificate_le _ _ _
  · rw [Circuit.eval_eq_evalOutput, ← hy, houtput, show c.code.1 = r.1 by rw [hc]]
    exact hall t ht

/-- A circuit of size at most `S` meeting the acceptance condition on every test in `tests` has a
certificate of length `certLength m S`, accepted by `checkCertificateOn` whatever bits follow
it. -/
theorem exists_checkCertificateOn_append {α : Type} {tests : List α}
    {input : α → List Bool} {accept : α → Bool → Bool}
    {m S : ℕ} {C : Circuit signature m 1} (hcS : C.size ≤ S)
    (haccept : ∀ t ∈ tests, ∃ y : BitString m, input t = List.ofFn y ∧
      accept t (C.eval interpretation y 0) = true) :
    ∃ u : List Bool, u.length = certLength m S ∧
      ∀ extra, checkCertificateOn tests input accept m S (u ++ extra) = true := by
  have hcode : Program.IsCodeFrom signature m 0 C.code.1 := by
    rw [← Program.isSome_ofCode_iff, Circuit.code, Program.ofCode_code]
    rfl
  refine ⟨certificate m S C.code.1 (C.outputs 0).toNat, length_certificate_code C hcS,
    fun extra => ?_⟩
  simp only [checkCertificateOn, validCertificate, evalCertificate,
    readCertificate_certificate_code_append C hcS,
    Bool.and_eq_true, codeCheck_eq_true_iff.2 hcode, decide_eq_true_eq, List.all_eq_true,
    true_and]
  refine ⟨by rw [Circuit.length_code_fst]; exact (C.outputs 0).toNat_lt, fun t ht => ?_⟩
  obtain ⟨y, hy, hacc⟩ := haccept t ht
  rw [hy, ← Circuit.eval_eq_evalOutput]
  exact hacc

/-- An accepted certificate decoded by `checkCertificate` describes a circuit of size at most `S`
meeting the acceptance condition on every input. -/
theorem exists_circuit_of_checkCertificate {accept : List Bool → Bool → Bool}
    {m S : ℕ} {w : List Bool} (hw : checkCertificate accept m S w = true) :
    ∃ C : Circuit signature m 1, C.size ≤ S ∧
      ∀ y : BitString m, accept (List.ofFn y) (C.eval interpretation y 0) = true := by
  obtain ⟨c, hcS, hall⟩ := exists_circuit_of_checkCertificateOn hw
  exact ⟨c, hcS, fun y => hall (List.ofFn y) (BitString.mem_enumList.2 List.length_ofFn) y rfl⟩

/-- A circuit of size at most `S` meeting the acceptance condition has a certificate of length
`certLength m S`, accepted whatever bits follow it. -/
theorem exists_checkCertificate_append {accept : List Bool → Bool → Bool}
    {m S : ℕ} {C : Circuit signature m 1} (hcS : C.size ≤ S)
    (haccept : ∀ y : BitString m, accept (List.ofFn y) (C.eval interpretation y 0) = true) :
    ∃ u : List Bool, u.length = certLength m S ∧
      ∀ extra, checkCertificate accept m S (u ++ extra) = true := by
  refine exists_checkCertificateOn_append hcS fun y hy => ?_
  obtain ⟨y', rfl⟩ : ∃ y' : BitString m, List.ofFn y' = y :=
    ⟨fun i => y[i.val]'(by rw [BitString.mem_enumList.1 hy]; exact i.isLt),
      List.ext_getElem (by simp [BitString.mem_enumList.1 hy]) fun _ _ _ => by simp⟩
  exact ⟨y', rfl, haccept y'⟩

/-- Soundness of `validCertificate`: a well-formed certificate for `(n, s)` decodes to a circuit of
size at most `s` whose evaluation agrees with `evalCertificate`. -/
theorem exists_circuit_of_validCertificate {n s : ℕ} {w : List Bool}
    (hw : validCertificate n s w = true) :
    ∃ C : Circuit signature n 1, C.size ≤ s ∧
      ∀ x : BitString n, C.eval interpretation x 0 = evalCertificate n s w (List.ofFn x) := by
  have hcheck : checkCertificate (fun y out => out == evalCertificate n s w y) n s w = true := by
    simp [checkCertificate, checkCertificateOn, hw]
  obtain ⟨C, hcS, heval⟩ := exists_circuit_of_checkCertificate hcheck
  exact ⟨C, hcS, fun x => beq_iff_eq.1 (heval x)⟩

/-- Completeness of `validCertificate`: every circuit of size at most `s` on `n` inputs has a
canonical certificate of length `certLength n s` satisfying `validCertificate` whose
`evalCertificate` agrees with the circuit on all `n`-bit inputs. -/
theorem exists_validCertificate_of_circuit {n s : ℕ} (C : Circuit signature n 1)
    (hcS : C.size ≤ s) :
    ∃ w : List Bool, w.length = certLength n s ∧ validCertificate n s w = true ∧
      ∀ x : BitString n, evalCertificate n s w (List.ofFn x) = C.eval interpretation x 0 := by
  obtain ⟨w, hlen, hcheck⟩ := exists_checkCertificate_append
    (accept := fun y out => out == C.eval interpretation (BitString.ofList n y) 0) hcS
    (fun y => by simp)
  have hw := hcheck []
  rw [List.append_nil] at hw
  simp only [checkCertificate, checkCertificateOn, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at hw
  refine ⟨w, hlen, hw.1, fun x => ?_⟩
  simpa using hw.2 (List.ofFn x) (BitString.mem_enumList.2 List.length_ofFn)

/-- The verifier for MCSP: the certificate must describe a circuit on `n` inputs with at most
`budget n s` gates (`readCertificate`) that agrees with the truth table on all `2 ^ n` inputs. -/
def verifier (p : Instance × List Bool) : Bool :=
  checkCertificate (fun y out => out == tableValue (List.ofFn p.1.table) y)
    p.1.arity (budget p.1.arity p.1.threshold) p.2

/-! ### Correctness -/

/-- Generic truth-table indexing into a function represented as a list via `List.ofFn`. -/
theorem getD_boundedBinaryValue_reverse_ofFn {α : Type*} {n : ℕ} (T : Fin (2 ^ n) → α)
    (y : BitString n) (default : α) :
    (List.ofFn T).getD (BitString.boundedBinaryValue (List.ofFn T).length (List.ofFn y).reverse)
      default = T (BitString.equivFin n y) := by
  have hlt := (BitString.equivFin n y).isLt
  rw [BitString.boundedBinaryValue_eq, BitString.binaryValue_reverse_ofFn,
    List.length_ofFn, Nat.min_eq_right hlt.le, List.getD_ofFn_of_lt _ hlt]

/-- The verifier reads the function of an instance from its truth table. -/
theorem tableValue_ofFn (x : Instance) (y : BitString x.arity) :
    tableValue (List.ofFn x.table) (List.ofFn y) = x.function y :=
  getD_boundedBinaryValue_reverse_ofFn x.table y false

/-- The truth table of a function, as a list, is read back as the function. -/
@[simp] theorem tableFunction_ofFn_truthTable (m : ℕ) (f : BooleanFunction m) :
    tableFunction m (List.ofFn (truthTable m f)) = f := by
  funext y
  exact (tableValue_ofFn ⟨m, truthTable m f, 0⟩ y).trans (by simp [Instance.function])

/-- The polynomial bounding the length of certificates. -/
noncomputable def certPolynomial : Polynomial ℕ := 40 * (Polynomial.X + 1) ^ 4

/-- When the arity `n` and sample count `t` are each at most `L`, the certificate length at gate
budget `sampleBudget n t s` is bounded by `certPolynomial.eval L`. -/
theorem certLength_sampleBudget_le {n t s L : ℕ} (hn : n ≤ L) (ht : t ≤ L) :
    certLength n (sampleBudget n t s) ≤ certPolynomial.eval L := by
  have hS : sampleBudget n t s ≤ L * (2 * L + 3) + 1 :=
    (Nat.min_le_right _ _).trans (Nat.add_le_add_right
      (Nat.mul_le_mul ht (by omega)) 1)
  simp only [certPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, certLength]
  nlinarith

private theorem certLength_le (x : Instance) :
    certLength x.arity (budget x.arity x.threshold) ≤
      certPolynomial.eval (encInstance x).length :=
  have hT := two_pow_le_length_encInstance x
  certLength_sampleBudget_le ((Nat.lt_two_pow_self).le.trans hT) hT

/-- **Soundness of the verifier.** An instance with an accepted certificate, of any length, is
in MCSP. -/
theorem mem_of_verifier_eq_true {x : Instance} {w : List Bool} (hw : verifier (x, w) = true) :
    x ∈ MCSP := by
  obtain ⟨c, hcS, hall⟩ := exists_circuit_of_checkCertificate hw
  refine complexity_le_iff.2 ⟨c, Circuit.computes_single_iff.2 fun y => ?_, ?_⟩
  · have := hall y
    simp only [beq_iff_eq] at this
    rw [this, tableValue_ofFn]
  · exact hcS.trans (Nat.min_le_left _ _)

/-- **Completeness of the verifier.** Every instance in MCSP has a certificate of length
`certLength x.arity (budget x.arity x.threshold)` that is accepted whatever bits follow it. -/
theorem exists_verifier_append {x : Instance} (hx : x ∈ MCSP) :
    ∃ u : List Bool, u.length = certLength x.arity (budget x.arity x.threshold) ∧
      ∀ extra, verifier (x, u ++ extra) = true := by
  set S := budget x.arity x.threshold
  have hS : complexity interpretation (single x.function) ≤ S :=
    le_min hx (complexity_le_two_pow_mul_add_one _)
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation)
    (f := single x.function)
  have hcS : c.size ≤ S := hsize ▸ hS
  exact exists_checkCertificate_append
    (accept := fun y out => out == tableValue (List.ofFn x.table) y) hcS fun y => by
    rw [Circuit.computes_single_iff.1 hc y, tableValue_ofFn, beq_self_eq_true]

/-- `MCSP.verifier` verifies MCSP, with certificates of length `certPolynomial`. -/
theorem isVerifier : IsVerifier encInstance certPolynomial verifier MCSP := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_of_verifier_eq_true hw) fun x hx => ?_
  obtain ⟨u, hu, hV⟩ := exists_verifier_append hx
  exact ⟨u, hu ▸ certLength_le x, fun k => hV _⟩

/-! ### Polynomial time -/

open ComputableInPolyTime

/-- The verifier on the bits of a truth table, a threshold and a certificate, with the number of
inputs read from the length of the table: `MCSP.verifier` on raw data
(`Cslib.MCSP.verifier_eq_tableVerifier`), defined on every list of bits. -/
def tableVerifier (r : (List Bool × ℕ) × List Bool) : Bool :=
  let n := Nat.log 2 r.1.1.length
  checkCertificate (fun y out => out == tableValue r.1.1 y) n
    (sampleBudget n r.1.1.length r.1.2) r.2

theorem verifier_eq_tableVerifier (p : Instance × List Bool) :
    verifier p = tableVerifier ((List.ofFn p.1.table, p.1.threshold), p.2) := by
  simp only [tableVerifier, List.length_ofFn, Nat.log_pow Nat.one_lt_two]
  rfl

/-- The MCSP instance of a truth table of length `2 ^ m`. -/
private def tableInstance (m s : ℕ) (T : List Bool) (_hT : T.length = 2 ^ m) : Instance :=
  ⟨m, BitString.ofList (2 ^ m) T, s⟩

private theorem ofFn_tableInstance {m s : ℕ} {T : List Bool} (hT : T.length = 2 ^ m) :
    List.ofFn (tableInstance m s T hT).table = T :=
  BitString.ofFn_ofList hT

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

/-- Looking up an input in a truth table is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_tableValue :
    ComputableInPolyTime (fun p : List Bool × List Bool => tableValue p.1 p.2)
      (encPair encBits encBits) encBool := by
  unfold tableValue
  exact bitsGetDWithInput (fst encBits encBits)
    (bitsBoundedBinaryValueWithInput (length_bits.comp (fst encBits encBits))
      ((show ComputableInPolyTime List.reverse encBits encBits by fun_prop).comp
        (snd encBits encBits))) false

/-- Checking well-formedness of a certificate is computable in polynomial time when `m` and `S`
are given in unary. -/
@[fun_prop]
theorem computableInPolyTime_validCertificate {γ : Type} {encIn : γ ↪ List Bool}
    {m S : γ → ℕ} {w : γ → List Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hS : ComputableInPolyTime S encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun a => validCertificate (m a) (S a) (w a)) encIn encBool := by
  have hc := computableInPolyTime_readCertificate hm hS hw
  have hcode := computableInPolyTime_codeCheck hm hc.fst'
  have hbound : ComputableInPolyTime
      (fun a => decide ((readCertificate (m a) (S a) (w a)).2 <
        m a + (readCertificate (m a) (S a) (w a)).1.length))
      encIn encBool :=
    binary_lt' hc.snd' (unary_to_binary.comp (unary_add.comp
      (hm.prod ((length_list encGate).comp hc.fst'))))
  unfold validCertificate
  exact bool_and' hcode hbound

/-- Evaluating a certificate on an input is computable in polynomial time when `m` and `S` are
given in unary. -/
@[fun_prop]
theorem computableInPolyTime_evalCertificate {γ : Type} {encIn : γ ↪ List Bool}
    {m S : γ → ℕ} {w y : γ → List Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hS : ComputableInPolyTime S encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (hy : ComputableInPolyTime y encIn encBits) :
    ComputableInPolyTime (fun a => evalCertificate (m a) (S a) (w a) (y a)) encIn encBool := by
  have hc := computableInPolyTime_readCertificate hm hS hw
  exact computableInPolyTime_evalOutput hy hc.fst' hc.snd'

/-- A generic certificate verifier on a supplied list of tests is computable in polynomial time
when its test list, input extraction, and acceptance condition are polynomial-time. -/
theorem computableInPolyTime_checkCertificateOn {γ α : Type}
    {encIn : γ ↪ List Bool} {encTest : α ↪ List Bool}
    {tests : γ → List α} {input : α → List Bool}
    {m S : γ → ℕ} {w : γ → List Bool} {accept : γ → α → Bool → Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hS : ComputableInPolyTime S encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (htests : ComputableInPolyTime tests encIn (encList encTest))
    (hinput : ComputableInPolyTime input encTest encBits)
    (haccept : ComputableInPolyTime (fun p : (γ × α) × Bool => accept p.1.1 p.1.2 p.2)
      (encPair (encPair encIn encTest) encBool) encBool) :
    ComputableInPolyTime
      (fun a => checkCertificateOn (tests a) input (accept a) (m a) (S a) (w a))
      encIn encBool := by
  have hvalid := computableInPolyTime_validCertificate hm hS hw
  have hout : ComputableInPolyTime
      (fun p : γ × α => evalCertificate (m p.1) (S p.1) (w p.1) (input p.2))
      (encPair encIn encTest) encBool :=
    computableInPolyTime_evalCertificate (hm.comp (fst encIn encTest))
      (hS.comp (fst encIn encTest)) (hw.comp (fst encIn encTest))
      (hinput.comp (snd encIn encTest))
  have htest : ComputableInPolyTime
      (fun p : γ × α => accept p.1 p.2 (evalCertificate (m p.1) (S p.1) (w p.1) (input p.2)))
      (encPair encIn encTest) encBool :=
    haccept.comp ((id' (encIn := encPair encIn encTest)).prod hout)
  unfold checkCertificateOn
  simp only [List.all_eq_not_any_not]
  exact bool_and' hvalid (bool_not.comp (anyWithInput htests (bool_not.comp htest)))

/-- A generic certificate verifier is computable in polynomial time when its acceptance condition
is polynomial-time and the number of inputs is bounded by the input length. -/
theorem computableInPolyTime_checkCertificate {γ : Type} {encIn : γ ↪ List Bool}
    {m S : γ → ℕ} {w : γ → List Bool} {accept : γ → List Bool → Bool → Bool}
    (hm : ComputableInPolyTime m encIn encUnary)
    (hS : ComputableInPolyTime S encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    {size : ℕ → ℕ} (hsize : PolynomiallyBounded size)
    (hbudget : ∀ a, 2 ^ m a * (2 * m a + 1) ≤ size (encIn a).length)
    (haccept : ComputableInPolyTime (fun p : (γ × List Bool) × Bool => accept p.1.1 p.1.2 p.2)
      (encPair (encPair encIn encBits) encBool) encBool) :
    ComputableInPolyTime (fun a => checkCertificate (accept a) (m a) (S a) (w a))
      encIn encBool :=
  computableInPolyTime_checkCertificateOn hm hS hw
    (ComputableInPolyTime.bitsEnumList hm hsize hbudget)
    ComputableInPolyTime.id' haccept

/-- Computing `sampleBudget (m a) (t a) (s a)` in unary is polynomial-time when `m a` and `t a`
are polynomial-time in unary and `s a` is polynomial-time in binary. -/
theorem computableInPolyTime_sampleBudget {γ : Type} {encIn : γ ↪ List Bool}
    {m t s : γ → ℕ}
    (hm : ComputableInPolyTime m encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hs : ComputableInPolyTime s encIn encNat) :
    ComputableInPolyTime (fun a => sampleBudget (m a) (t a) (s a)) encIn encUnary := by
  have hcap : ComputableInPolyTime (fun a => t a * (2 * m a + 3) + 1) encIn encUnary := by
    fun_prop
  simpa only [sampleBudget, min_comm] using ComputableInPolyTime.binary_min_unary' hcap hs

/-- A certificate verifier on a table list, threshold, and certificate is computable in
polynomial time from `encPair (encPair encT encNat) encBits` when table length is computable
in polynomial time into unary, the encoding length bounds the table length, and the acceptance
condition is polynomial-time. -/
theorem computableInPolyTime_checkCertificate_table {α : Type} {encT : List α ↪ List Bool}
    {accept : List α → List Bool → Bool → Bool}
    (hlen : ComputableInPolyTime (fun T : List α => T.length) encT encUnary)
    (hlen_le : ∀ T : List α, T.length ≤ (encT T).length)
    (haccept : ComputableInPolyTime
      (fun p : (List α × List Bool) × Bool => accept p.1.1 p.1.2 p.2)
      (encPair (encPair encT encBits) encBool) encBool) :
    ComputableInPolyTime
      (fun r : (List α × ℕ) × List Bool =>
        checkCertificate (accept r.1.1) (Nat.log 2 r.1.1.length)
          (sampleBudget (Nat.log 2 r.1.1.length) r.1.1.length r.1.2) r.2)
      (encPair (encPair encT encNat) encBits) encBool := by
  let encIn := encPair (encPair encT encNat) encBits
  have hT : ComputableInPolyTime (fun r : (List α × ℕ) × List Bool => r.1.1)
      encIn encT := (fst encT encNat).comp (fst _ _)
  have hlen_r : ComputableInPolyTime (fun r : (List α × ℕ) × List Bool => r.1.1.length)
      encIn encUnary := hlen.comp hT
  have hm : ComputableInPolyTime (fun r : (List α × ℕ) × List Bool =>
      Nat.log 2 r.1.1.length) encIn encUnary := binary_log_two.comp (unary_to_binary.comp hlen_r)
  have hs : ComputableInPolyTime (fun r : (List α × ℕ) × List Bool => r.1.2)
      encIn encNat := (snd encT encNat).comp (fst _ _)
  have hS : ComputableInPolyTime (fun r : (List α × ℕ) × List Bool =>
      sampleBudget (Nat.log 2 r.1.1.length) r.1.1.length r.1.2) encIn encUnary :=
    computableInPolyTime_sampleBudget hm hlen_r hs
  have hw : ComputableInPolyTime (fun r : (List α × ℕ) × List Bool => r.2)
      encIn encBits := snd _ _
  have hsize : PolynomiallyBounded (fun L => L * L) := by fun_prop
  have hbudget (r : (List α × ℕ) × List Bool) :
      2 ^ Nat.log 2 r.1.1.length * (2 * Nat.log 2 r.1.1.length + 1) ≤
        (encIn r).length * (encIn r).length := by
    set T := r.1.1.length
    have hT_enc : 2 * T + 1 ≤ (encIn r).length := by
      have h1 := hlen_le r.1.1
      simp only [encIn, length_encPair]
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
      _ ≤ (encIn r).length * (encIn r).length :=
          Nat.mul_le_mul (by omega) hT_enc
  have hproj : ComputableInPolyTime
      (fun p : (((List α × ℕ) × List Bool) × List Bool) × Bool =>
        ((p.1.1.1.1, p.1.2), p.2))
      (encPair (encPair encIn encBits) encBool)
      (encPair (encPair encT encBits) encBool) :=
    (((fst _ _).fst'.fst'.fst').prod (fst _ _).snd').prod (snd _ _)
  have haccept_full : ComputableInPolyTime
      (fun p : (((List α × ℕ) × List Bool) × List Bool) × Bool => accept p.1.1.1.1 p.1.2 p.2)
      (encPair (encPair encIn encBits) encBool) encBool :=
    haccept.comp hproj
  exact computableInPolyTime_checkCertificate hm hS hw
    hsize hbudget haccept_full

/-- The verifier on raw data is polynomial-time. -/
theorem computableInPolyTime_tableVerifier : ComputableInPolyTime tableVerifier
    (encPair (encPair encBits encNat) encBits) encBool := by
  have hval : ComputableInPolyTime
      (fun p : (List Bool × List Bool) × Bool => tableValue p.1.1 p.1.2)
      (encPair (encPair encBits encBits) encBool) encBool :=
    computableInPolyTime_tableValue.comp ((fst _ _).fst'.prod (fst _ _).snd')
  have haccept : ComputableInPolyTime
      (fun p : (List Bool × List Bool) × Bool => p.2 == tableValue p.1.1 p.1.2)
      (encPair (encPair encBits encBits) encBool) encBool :=
    (snd _ _).beq hval
  exact computableInPolyTime_checkCertificate_table (accept := fun T y out => out == tableValue T y)
    length_bits (fun _ => le_rfl) haccept

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
