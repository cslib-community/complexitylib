/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Classical
public import Complexity.Computability.Circuit.Quantum.Uniform
public import Complexity.Computability.Circuit.Boolean.EvaluationTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD

/-!
# Reversible compilation of Boolean circuits

A De Morgan gate list (`Complexity/Computability/Circuit/Boolean/Encoding.lean`) on `n` inputs is
compiled into NOT, CNOT and Toffoli gate codes (`Cslib.Quantum.Reversible.codes`). Input `i` sits on
qubit `i` and gate `j` writes its value onto the fresh qubit `n + j`, the numbering of wires in
circuit codes. A constant gate is a NOT or nothing, a negation is a CNOT followed by a NOT, a
conjunction is a Toffoli gate, and a disjunction `a ∨ b = a ⊕ b ⊕ (a ∧ b)` is two CNOT gates and a
Toffoli gate. An argument that is missing, or that names a wire not computed before the gate, is
read from a qubit `z` that no gate writes, which stays zero; this matches `Cslib.Circuits.evalCode`,
which reads such arguments as `false`, so the compilation is correct for every gate list
(`Cslib.Quantum.Reversible.readBit_classicalRun_codes`). Nothing is uncomputed: the circuit is
measured once at the end, and only one qubit matters.

Wire numbers in circuit codes are binary; the compiler caps each argument by the unary number of its
gate before converting it, so it runs in polynomial time
(`Cslib.Quantum.Reversible.computableInPolyTime_codes`).

## Main definitions

* `Cslib.Quantum.Reversible.gateCodes`: the gate codes of one De Morgan gate.
* `Cslib.Quantum.Reversible.codes`: the gate codes of a De Morgan gate list.

## Main results

* `Cslib.Quantum.Reversible.isClassical_codes`: the compiled circuit is classical.
* `Cslib.Quantum.Reversible.readBit_classicalRun_codes`: it computes the wire values of the gate
  list.
* `Cslib.Quantum.Reversible.computableInPolyTime_codes`: it is compiled in polynomial time.
-/

@[expose] public section

namespace Cslib.Quantum.Reversible

open Circuits Circuits.Boolean GateCode Turing.MultiTapeTM

/-- Argument `i` of a gate whose wire is `t`, capped at `t`; `t` when the argument is missing. -/
def capArg (t : ℕ) (args : List ℕ) (i : ℕ) : ℕ :=
  if i < args.length then min t (args.getD i 0) else t

/-- The qubit read for argument `i` of a gate writing qubit `t`: the wire it names, when that wire
is computed before the gate, and the zero qubit `z` otherwise. -/
def argQubit (z t : ℕ) (args : List ℕ) (i : ℕ) : ℕ :=
  if capArg t args i < t then capArg t args i else z

/-- The gate codes computing the De Morgan gate `g` onto the fresh qubit `t`, reading missing or
not yet computed arguments from the zero qubit `z`. -/
def gateCodes (z t : ℕ) (g : Op × List ℕ) : List GateCode :=
  match g.1 with
  | .const b => if b then [(false, t, [])] else []
  | .not => [(false, t, [argQubit z t g.2 0]), (false, t, [])]
  | .and =>
    if argQubit z t g.2 0 = argQubit z t g.2 1 then [(false, t, [argQubit z t g.2 0])]
    else [(false, t, [argQubit z t g.2 0, argQubit z t g.2 1])]
  | .or =>
    if argQubit z t g.2 0 = argQubit z t g.2 1 then [(false, t, [argQubit z t g.2 0])]
    else [(false, t, [argQubit z t g.2 0]), (false, t, [argQubit z t g.2 1]),
      (false, t, [argQubit z t g.2 0, argQubit z t g.2 1])]

/-- **The reversible compilation** of a De Morgan gate list on `n` inputs: gate `j` is computed
onto qubit `n + j`, with `z` the zero qubit. -/
def codes (n z : ℕ) (gates : List (Op × List ℕ)) : List GateCode :=
  gates.zipIdx.flatMap fun p => gateCodes z (n + p.2) p.1

theorem codes_append_singleton (n z : ℕ) (gates : List (Op × List ℕ)) (g : Op × List ℕ) :
    codes n z (gates ++ [g]) = codes n z gates ++ gateCodes z (n + gates.length) g := by
  simp [codes, List.zipIdx_append]

/-! ### Correctness -/

variable {W : ℕ}

theorem argQubit_lt_or_eq (z t : ℕ) (args : List ℕ) (i : ℕ) :
    argQubit z t args i < t ∨ argQubit z t args i = z := by
  unfold argQubit
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr rfl

/-- **The qubit read for an argument holds its value**, when the qubits hold the wire values
`vals` computed before the gate. -/
theorem readBit_argQubit {z t : ℕ} (hz : t ≤ z) {Y : Fin W → Bool} {vals : List Bool}
    (hvals : vals.length = t) (hY : ∀ p, readBit Y p = vals.getD p false) (args : List ℕ)
    (i : ℕ) : readBit Y (argQubit z t args i) = args[i]?.elim false (vals.getD · false) := by
  have hfalse (p : ℕ) (hp : t ≤ p) : vals.getD p false = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  unfold argQubit capArg
  by_cases hi : i < args.length
  · rw [List.getElem?_eq_getElem hi, Option.elim_some, List.getD_eq_getElem _ _ hi]
    simp only [hi, ite_true]
    by_cases ha : args[i] < t
    · rw [min_eq_right ha.le, ite_eq_left ha, hY]
    · rw [min_eq_left (not_lt.mp ha), ite_eq_right (lt_irrefl t), hY, hfalse z hz,
        hfalse _ (not_lt.mp ha)]
  · rw [List.getElem?_eq_none (not_lt.mp hi)]
    simp only [hi, ite_false, lt_irrefl, Option.elim_none]
    rw [hY, hfalse z hz]

theorem isClassical_gateCodes {z t : ℕ} (htz : t < z) (hz : z < W) (g : Op × List ℕ) :
    IsClassical W (gateCodes z t g) := by
  have ha (i : ℕ) := argQubit_lt_or_eq z t g.2 i
  have ht : t < W := htz.trans hz
  have hlt (i : ℕ) : argQubit z t g.2 i < W := by rcases ha i with h | h <;> omega
  have hne (i : ℕ) : t ≠ argQubit z t g.2 i := by rcases ha i with h | h <;> omega
  have hnot : WellFormed W ((false, t, []) : GateCode) := ⟨by simp, by simp, by simpa using ht⟩
  have hcnot (i : ℕ) : WellFormed W ((false, t, [argQubit z t g.2 i]) : GateCode) :=
    ⟨by simp, by simpa using hne i, by simpa [ht] using hlt i⟩
  have htof (h : argQubit z t g.2 0 ≠ argQubit z t g.2 1) :
      WellFormed W ((false, t, [argQubit z t g.2 0, argQubit z t g.2 1]) : GateCode) :=
    ⟨by simp, by simp [hne 0, hne 1, h], by simp [ht, hlt 0, hlt 1]⟩
  intro c hc
  obtain ⟨op, args⟩ := g
  cases op with
  | const b =>
    cases b
    · simp only [gateCodes, Bool.false_eq_true, ite_false, List.not_mem_nil] at hc
    · simp only [gateCodes, ite_true, List.mem_singleton] at hc
      exact hc ▸ ⟨rfl, hnot⟩
  | not =>
    simp only [gateCodes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨rfl, hcnot 0⟩
    · exact ⟨rfl, hnot⟩
  | and =>
    simp only [gateCodes] at hc
    split_ifs at hc with h
    · exact (List.mem_singleton.mp hc) ▸ ⟨rfl, hcnot 0⟩
    · exact (List.mem_singleton.mp hc) ▸ ⟨rfl, htof h⟩
  | or =>
    simp only [gateCodes] at hc
    split_ifs at hc with h
    · exact (List.mem_singleton.mp hc) ▸ ⟨rfl, hcnot 0⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact ⟨rfl, hcnot 0⟩
      · exact ⟨rfl, hcnot 1⟩
      · exact ⟨rfl, htof h⟩

/-- **One compiled gate appends its value**: if the qubits hold the wire values `vals` computed
before the gate `g` and zeros after them, its codes add the value of `g` on qubit `t`. -/
theorem readBit_classicalRun_gateCodes {z t : ℕ} (htz : t < z) (hz : z < W)
    {Y : Fin W → Bool} {vals : List Bool} (hvals : vals.length = t)
    (hY : ∀ p, readBit Y p = vals.getD p false) (g : Op × List ℕ) (p : ℕ) :
    readBit (classicalRun (gateCodes z t g) Y) p =
      (vals ++ [interpretation g.1 fun a => g.2[a.val]?.elim false (vals.getD · false)]).getD p
        false := by
  have hread : ∀ c ∈ gateCodes z t g, ∀ c' ∈ gateCodes z t g, c.2.1 ∉ c'.2.2 := by
    have hne (i : ℕ) : t ≠ argQubit z t g.2 i := by
      rcases argQubit_lt_or_eq z t g.2 i with h | h <;> omega
    intro c hc c' hc'
    obtain ⟨op, args⟩ := g
    cases op with
    | const b => cases b <;> simp_all [gateCodes]
    | not => simp only [gateCodes, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
             rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> simp [hne 0]
    | and =>
      simp only [gateCodes] at hc hc'
      split_ifs at hc hc' <;> simp only [List.mem_singleton] at hc hc' <;> subst hc hc' <;>
        simp [hne 0, hne 1]
    | or =>
      simp only [gateCodes] at hc hc'
      split_ifs at hc hc' <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hc' <;>
        (try rcases hc with rfl | rfl | rfl) <;> (try rcases hc' with rfl | rfl | rfl) <;>
        simp [hne 0, hne 1]
  rw [readBit_classicalRun_of_forall_notMem (isClassical_gateCodes htz hz g) hread, hY]
  have harg (i : ℕ) := readBit_argQubit htz.le hvals hY g.2 i
  have hget : (vals ++ [interpretation g.1 fun a => g.2[a.val]?.elim false
      (vals.getD · false)]).getD p false =
      if p = t then interpretation g.1 fun a => g.2[a.val]?.elim false (vals.getD · false)
      else vals.getD p false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    split_ifs with hp
    · subst hp
      simp [hvals]
    · rcases lt_or_gt_of_ne hp with h | h
      · rw [List.getElem?_append_left (by omega)]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  rw [hget]
  have ht : vals.getD t false = false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  obtain ⟨op, args⟩ := g
  by_cases hp : p = t
  · subst p
    rw [ht, show (interpretation op fun a => args[a.val]?.elim false (vals.getD · false)) =
      interpretation op fun a => readBit Y (argQubit z t args a) from
      congrArg _ (funext fun a => (harg a).symm)]
    cases op with
    | const b => cases b <;> simp [gateCodes, interpretation]
    | not => simp [gateCodes, interpretation]
    | and =>
      simp only [gateCodes]
      split_ifs with h
      · simp [interpretation, ← h]
      · simp [interpretation]
    | or =>
      simp only [gateCodes]
      split_ifs with h
      · simp [interpretation, ← h]
      · simp only [List.foldl_cons, List.foldl_nil, List.all_cons, List.all_nil,
          decide_true, Bool.true_and, Bool.and_true, Bool.false_xor, interpretation,
          Fin.val_zero, Fin.val_one]
        cases readBit Y (argQubit z t args 0) <;> cases readBit Y (argQubit z t args 1) <;> rfl
  · rw [ite_eq_right hp]
    cases op with
    | const b => cases b <;> simp [gateCodes, hp]
    | not => simp [gateCodes, hp]
    | and =>
      simp only [gateCodes]
      split_ifs <;> simp [hp]
    | or =>
      simp only [gateCodes]
      split_ifs <;> simp [hp]

theorem isClassical_codes {n z : ℕ} {gates : List (Op × List ℕ)} (hz : n + gates.length ≤ z)
    (hW : z < W) : IsClassical W (codes n z gates) := by
  refine IsClassical.flatMap fun p hp => isClassical_gateCodes ?_ hW p.1
  have := (List.mem_zipIdx hp).2.1
  omega

/-- **The compiled circuit computes the gate list's wire values**: started from the input bits
`xs` and zeros, qubit `p` ends with the value of wire `p` (`false` past the last wire). -/
theorem readBit_classicalRun_codes {n z : ℕ} {gates : List (Op × List ℕ)}
    (hz : n + gates.length ≤ z) (hW : z < W) {xs : List Bool} (hxs : xs.length = n)
    {X : Fin W → Bool} (hX : ∀ p, readBit X p = xs.getD p false) (p : ℕ) :
    readBit (classicalRun (codes n z gates) X) p =
      (evalCode interpretation false xs gates).getD p false := by
  induction gates using List.reverseRecOn generalizing p with
  | nil => rw [codes, List.zipIdx_nil, List.flatMap_nil, classicalRun_nil, evalCode_nil, hX]
  | append_singleton gates g ih =>
    simp only [List.length_append, List.length_singleton] at hz
    rw [codes_append_singleton, classicalRun_append, evalCode_append_singleton]
    exact readBit_classicalRun_gateCodes (by omega) hW (by simp [hxs]) (ih (by omega)) g p

/-! ### Polynomial time -/

variable {γ : Type} {enc : γ ↪ List Bool}

/-- One gate written with decisions on its operation, for polynomial-time compilation. -/
private theorem gateCodes_eq (z t : ℕ) (g : Op × List ℕ) :
    gateCodes z t g =
      if g.1 = .const true then [(false, t, [])]
      else if g.1 = .not then [(false, t, [argQubit z t g.2 0]), (false, t, [])]
      else if g.1 = .and then
        (if argQubit z t g.2 0 = argQubit z t g.2 1 then [(false, t, [argQubit z t g.2 0])]
        else [(false, t, [argQubit z t g.2 0, argQubit z t g.2 1])])
      else if g.1 = .or then
        (if argQubit z t g.2 0 = argQubit z t g.2 1 then [(false, t, [argQubit z t g.2 0])]
        else [(false, t, [argQubit z t g.2 0]), (false, t, [argQubit z t g.2 1]),
          (false, t, [argQubit z t g.2 0, argQubit z t g.2 1])])
      else [] := by
  obtain ⟨op, args⟩ := g
  cases op with
  | const b => cases b <;> simp [gateCodes]
  | not => simp [gateCodes]
  | and => simp [gateCodes]
  | or => simp [gateCodes]

theorem computableInPolyTime_gateCodes {z t : γ → ℕ} {g : γ → Op × List ℕ}
    (hz : ComputableInPolyTime z enc encUnary) (ht : ComputableInPolyTime t enc encUnary)
    (hg : ComputableInPolyTime g enc encGate) :
    ComputableInPolyTime (fun c => gateCodes (z c) (t c) (g c)) enc (encList encGateCode) := by
  have harg (i : ℕ) : ComputableInPolyTime (fun c => argQubit (z c) (t c) (g c).2 i) enc
      encUnary := by
    unfold argQubit capArg
    fun_prop
  have h₀ := harg 0
  have h₁ := harg 1
  simp only [gateCodes_eq]
  fun_prop

/-- **The reversible compilation runs in polynomial time.** -/
theorem computableInPolyTime_codes {n z : γ → ℕ} {gates : γ → List (Op × List ℕ)}
    (hn : ComputableInPolyTime n enc encUnary) (hz : ComputableInPolyTime z enc encUnary)
    (hgates : ComputableInPolyTime gates enc (encList encGate)) :
    ComputableInPolyTime (fun c => codes (n c) (z c) (gates c)) enc (encList encGateCode) := by
  have hg : ComputableInPolyTime (fun q : γ × ((Op × List ℕ) × ℕ) =>
      gateCodes (z q.1) (n q.1 + q.2.2) q.2.1) (encPair enc (encPair encGate encUnary))
      (encList encGateCode) :=
    computableInPolyTime_gateCodes (by fun_prop) (by fun_prop) (by fun_prop)
  unfold codes
  fun_prop

end Cslib.Quantum.Reversible
