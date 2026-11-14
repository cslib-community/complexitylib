/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.RealEncoding
public import CslibFrontier.Computability.Circuit.Quantum.Uniform
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Quantum circuits with phase gates, simulated by real circuits

The gate set of `Cslib.Complexity.BQP` consists of the Hadamard gate and the classical reversible
gates NOT, CNOT and Toffoli, whose matrices are real. This file adds the controlled phase gates
(`Cslib.Quantum.Gate.ctrlPhase`): the phase gate `S = P(i) = diag(1, i)`, the controlled phase gate
`Λ(P(i)) = diag(1, 1, 1, i)`, and their inverses. A gate code of the extended set
(`Cslib.Quantum.PhaseGateCode`) is either a gate code `(false, g)` (`Cslib.Quantum.GateCode`) or a
controlled phase gate `(true, (inv, t, cs))` on the qubits `t :: cs`, with at most one control.
Uniform families over the extended set (`Cslib.Quantum.UniformPhaseCircuitFamily`) are defined as
uniform families of circuits are. The extended set contains `{Λ(P(i)), H}`, which Kitaev proved
universal [Kitaev1997]; this is Theorem 1 of [Aharonov][Aharonov2003].

**The real simulation.** A circuit is turned into a real one by adding a qubit that records
whether a real or an imaginary part is stored; Aharonov attributes this to
[Bernstein, Vazirani][BernsteinVazirani1997]. The real version of a gate `U` is Definition 1 of
[Aharonov][Aharonov2003], and its entries are the blocks `Cslib.Quantum.realEntry`. Through this
encoding (`CslibFrontier/Computability/Circuit/Quantum/RealEncoding.lean`), with the encoding qubit
`r` after the register, the real gates simulate themselves, and a controlled phase gate on the
qubits `qs` becomes the rotation `J = [[0, -1], [1, 0]]` of `r` controlled by `qs`. Since
`J = X Z` and `Z = H X H`, it is the gate sequence `H_r, X_{qs → r}, H_r, X_{qs → r}`, where the
middle gates are CNOT or Toffoli gates flipping `r`; its inverse `J⁻¹ = Z X` is the reversed
sequence (`Cslib.Quantum.PhaseGateCode.phaseCodes`). For `Λ(P(i))` this is the decomposition
`Λ²[XZ] = T(1, 2, 3) H(3) T(1, 2, 3) H(3)` in the proof of Theorem 2 of [Aharonov][Aharonov2003].

So every circuit with controlled phase gates is simulated exactly by a circuit of at most four
times as many Hadamard, NOT, CNOT and Toffoli gates on one more qubit
(`Cslib.Quantum.PhaseGateCode.realSimulates_toRealCodes`), which measures the original qubits with
the same probabilities (`Cslib.Quantum.PhaseGateCode.onesProb_toRealCodes`). For uniform families
the translation is computed in polynomial time and preserves acceptance probabilities exactly
(`Cslib.Quantum.UniformPhaseCircuitFamily.realify`,
`Cslib.Quantum.UniformPhaseCircuitFamily.acceptProb_realify`).

**Scope.** This is the reduction step of Aharonov's proof that `{T, H}` is computationally
universal (her Theorem 2). Its other ingredient, Kitaev's universality of `{Λ(P(i)), H}`, and the
Solovay–Kitaev theorem behind computational universality are not formalized here. The simulation
is stated for the gates of the extended set; the real version of an arbitrary gate is not
constructed as a placed gate.

## Main definitions

* `Cslib.Quantum.Gate.ctrlPhase`: the controlled phase gate on `k` qubits.
* `Cslib.Quantum.PlacedGate.ctrlPhase`: a controlled phase gate or its inverse on chosen qubits.
* `Cslib.Quantum.PhaseGateCode`, `Cslib.Quantum.PhaseGateCode.WellFormed`,
  `Cslib.Quantum.PhaseGateCode.toPlacedGate?`, `Cslib.Quantum.Circuit.ofPhaseCodes`: gate codes
  with controlled phase gates and the circuits they denote.
* `Cslib.Quantum.PhaseGateCode.onesProb`, `Cslib.Quantum.PhaseGateCode.acceptProb`: measurement
  probabilities, as `Cslib.Quantum.onesProb` and `Cslib.Quantum.acceptProb`.
* `Cslib.Quantum.PhaseGateCode.phaseCodes`, `Cslib.Quantum.PhaseGateCode.realCodes`,
  `Cslib.Quantum.PhaseGateCode.toRealCodes`: the real translation.
* `Cslib.Quantum.encPhaseGateCode`, `Cslib.Quantum.UniformPhaseCircuitFamily`: uniform families
  with controlled phase gates.
* `Cslib.Quantum.UniformPhaseCircuitFamily.realify`: the real simulation of such a family.
* `Cslib.Quantum.UniformCircuitFamily.toPhaseFamily`: a family without phase gates, as one with
  phase gates.

## Main results

* `Cslib.Quantum.PlacedGate.eval_ctrlPhase_ket`: a controlled phase gate on a basis state.
* `Cslib.Quantum.GateCode.im_toPlacedGate?_gate`: the gates of gate codes are real.
* `Cslib.Quantum.PhaseGateCode.realSimulates_phaseCodes`: four Hadamard and classical gates
  simulate a controlled phase gate.
* `Cslib.Quantum.PhaseGateCode.realSimulates_toRealCodes`: the real translation simulates the
  circuit.
* `Cslib.Quantum.PhaseGateCode.onesProb_toRealCodes`,
  `Cslib.Quantum.PhaseGateCode.acceptProb_toRealCodes`: it measures the original qubits with the
  same probabilities.
* `Cslib.Quantum.UniformPhaseCircuitFamily.acceptProb_realify`,
  `Cslib.Quantum.UniformCircuitFamily.acceptProb_toPhaseFamily`: the translations between the two
  kinds of families preserve acceptance probabilities.

## References

* [D. Aharonov, *A simple proof that Toffoli and Hadamard are quantum universal*][Aharonov2003],
  arXiv:quant-ph/0301040v1, Definition 1, Theorems 1 and 2
* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
* [A. Yu. Kitaev, *Quantum computations: algorithms and error correction*][Kitaev1997]
-/

public section

namespace Cslib.Quantum

open Matrix Finset Turing.MultiTapeTM

variable {m : ℕ}

/-! ### Controlled phase gates -/

namespace Gate

/-- The **controlled phase gate** on `k` qubits: it multiplies `|x⟩` by `i` when every qubit is
one. For `k = 1` this is the phase gate `S = P(i) = diag(1, i)`, and for `k = 2` the controlled
phase gate `Λ(P(i)) = diag(1, 1, 1, i)`. -/
noncomputable def ctrlPhase (k : ℕ) : Gate k :=
  ⟨diagonal fun x => if ∀ i, x i = true then Complex.I else 1, by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1 with x : 1
    by_cases h : ∀ i, x i = true <;> simp [h]⟩

/-- The entries of the controlled phase gate (`inv = false`) and of its inverse (`inv = true`):
the diagonal entry of `|x⟩` is `i`, respectively `-i`, when every qubit of `x` is one, and `1`
otherwise. -/
theorem ctrlPhase_cond_apply (k : ℕ) (inv : Bool) (y x : Fin k → Bool) :
    ((bif inv then (ctrlPhase k)⁻¹ else ctrlPhase k : Gate k) :
      Matrix (Fin k → Bool) (Fin k → Bool) ℂ) y x =
      if y = x then (if ∀ i, x i = true then (bif inv then -Complex.I else Complex.I) else 1)
      else 0 := by
  by_cases hyx : y = x
  · subst hyx
    cases inv <;> by_cases h : ∀ i, y i = true <;> simp [ctrlPhase, h]
  · cases inv <;> simp [ctrlPhase, hyx, Ne.symm hyx]

end Gate

/-- The controlled phase gate, or for `inv` its inverse, on the qubits `e`. -/
noncomputable def PlacedGate.ctrlPhase (inv : Bool) {k : ℕ} (e : Fin k ↪ Fin m) : PlacedGate m :=
  ⟨k, bif inv then (Gate.ctrlPhase k)⁻¹ else Gate.ctrlPhase k, e⟩

/-- Moving a controlled phase gate to a larger register composes its wire placement. -/
@[simp] theorem PlacedGate.mapWires_ctrlPhase {N k : ℕ} (e : Fin m ↪ Fin N) (inv : Bool)
    (A : Fin k ↪ Fin m) :
    (PlacedGate.ctrlPhase inv A).mapWires e = PlacedGate.ctrlPhase inv (A.trans e) := by
  unfold PlacedGate.ctrlPhase PlacedGate.mapWires
  rfl

/-- **The entries of a placed controlled phase gate**: it multiplies `|x⟩` by `i` (for `inv`, by
`-i`) when every qubit of `e` is one. -/
theorem PlacedGate.ctrlPhase_matrix_apply (inv : Bool) {k : ℕ} (e : Fin k ↪ Fin m)
    (y x : Fin m → Bool) :
    ((PlacedGate.ctrlPhase inv e).matrix : Matrix _ _ ℂ) y x =
      if y = x then (if ∀ i, x (e i) = true then (bif inv then -Complex.I else Complex.I) else 1)
      else 0 := by
  rw [show PlacedGate.ctrlPhase inv e =
      ⟨k, bif inv then (Gate.ctrlPhase k)⁻¹ else Gate.ctrlPhase k, e⟩ from rfl, matrix_apply]
  dsimp only
  rw [Gate.ctrlPhase_cond_apply]
  simp only [Function.comp_apply]
  by_cases hyx : y = x
  · subst hyx
    simp
  · rw [ite_eq_right hyx]
    have key (h₁ : ∀ j, (¬∃ i, e i = j) → y j = x j) (h₂ : y ∘ e = x ∘ e) : y = x :=
      funext fun j => by
        by_cases hj : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := hj
          exact congrFun h₂ i
        · exact h₁ j hj
    split_ifs with h₁ h₂ <;> first | rfl | exact absurd (key h₁ h₂) hyx

/-- **A controlled phase gate multiplies a basis state** by `i` (for `inv`, by `-i`) when every
qubit of `e` is one. -/
theorem PlacedGate.eval_ctrlPhase_ket (inv : Bool) {k : ℕ} (e : Fin k ↪ Fin m) (x : Fin m → Bool) :
    (PlacedGate.ctrlPhase inv e).eval (ket x) =
      (if ∀ i, x (e i) = true then (bif inv then -Complex.I else Complex.I) else 1) • ket x := by
  ext y
  rw [PlacedGate.eval_ket_apply, PlacedGate.ctrlPhase_matrix_apply, WithLp.ofLp_smul,
    Pi.smul_apply, ket_apply, smul_eq_mul]
  by_cases h : y = x <;> simp [h]

/-! ### Gate codes on a larger register -/

namespace GateCode

/-- **The gates of gate codes are real**: the Hadamard gate and the classical reversible gates
have real entries. -/
theorem im_toPlacedGate?_gate {g : GateCode} {p : PlacedGate m}
    (hp : toPlacedGate? m g = some p) (y x : Fin p.arity → Bool) :
    ((p.gate : Matrix (Fin p.arity → Bool) (Fin p.arity → Bool) ℂ) y x).im = 0 := by
  have hperm {k : ℕ} (σ : Equiv.Perm (Fin k → Bool)) (y x : Fin k → Bool) :
      ((Gate.ofPerm σ : Matrix _ _ ℂ) y x).im = 0 := by
    rw [Gate.ofPerm_apply]
    split_ifs <;> simp
  match g, hp with
  | (true, t, []), hp =>
    simp only [toPlacedGate?] at hp
    split_ifs at hp
    simp only [Option.some.injEq] at hp
    subst hp
    change ((Gate.hadamard : Matrix _ _ ℂ) y x).im = 0
    rw [Gate.hadamard_apply]
    split_ifs <;> simp
  | (true, t, _ :: _), hp => simp [toPlacedGate?] at hp
  | (false, t, []), hp =>
    simp only [toPlacedGate?] at hp
    split_ifs at hp
    simp only [Option.some.injEq] at hp
    subst hp
    exact hperm _ y x
  | (false, t, [c]), hp =>
    simp only [toPlacedGate?] at hp
    split_ifs at hp
    simp only [Option.some.injEq] at hp
    subst hp
    exact hperm _ y x
  | (false, t, [c₁, c₂]), hp =>
    simp only [toPlacedGate?] at hp
    split_ifs at hp
    simp only [Option.some.injEq] at hp
    subst hp
    exact hperm _ y x
  | (false, t, _ :: _ :: _ :: _), hp => simp [toPlacedGate?] at hp

/-- **A gate code simulates itself** through the real encoding, on one more qubit. -/
theorem realSimulates_ofCodes {g : GateCode} (hg : g.WellFormed m) :
    (Circuit.ofCodes (m + 1) [g]).RealSimulates (Circuit.ofCodes m [g]) := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (isSome_toPlacedGate?_iff.mpr hg)
  have hp' : toPlacedGate? (m + 1) g = some (p.mapWires Fin.castSuccEmb) := by
    have h := toPlacedGate?_shift (o := 0) (N := m + 1) (by omega) hg
    rw [shift_zero, hp, Option.map_some] at h
    exact h
  simp only [Circuit.ofCodes, List.filterMap_cons, hp, hp', List.filterMap_nil]
  exact p.realSimulates_mapWires_castSuccEmb (im_toPlacedGate?_gate hp)

end GateCode

/-! ### Gate codes with controlled phase gates -/

/-- A **gate code with phase gates**: `(false, g)` is the gate code `g` (`Cslib.Quantum.GateCode`),
and `(true, (inv, t, cs))` with at most one control `cs` is the controlled phase gate on the qubits
`t :: cs` (`Cslib.Quantum.Gate.ctrlPhase`): the phase gate `S = diag(1, i)` on qubit `t` when
`cs = []`, and the controlled phase gate `Λ(S)` on the qubits `c` and `t` when `cs = [c]`; inverted
when `inv` is true. -/
abbrev PhaseGateCode := Bool × GateCode

namespace PhaseGateCode

/-- The placed gate denoted by a gate code with phase gates on `m` qubits, or `none` when the code
is not well formed. -/
@[expose] noncomputable def toPlacedGate? (m : ℕ) : PhaseGateCode → Option (PlacedGate m)
  | (false, g) => GateCode.toPlacedGate? m g
  | (true, inv, t, []) =>
    if h : t < m then
      some (PlacedGate.ctrlPhase inv ⟨![⟨t, h⟩], fun i j _ => Subsingleton.elim i j⟩)
    else none
  | (true, inv, t, [c]) =>
    if h : c < m ∧ t < m ∧ c ≠ t then
      some (PlacedGate.ctrlPhase inv ⟨![⟨c, h.1⟩, ⟨t, h.2.1⟩], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> first | rfl | (simp [Fin.ext_iff] at hij; omega)⟩)
    else none
  | (true, _, _, _ :: _ :: _) => none

/-- A gate code with phase gates is **well formed** on `m` qubits: a well-formed gate code, or a
phase gate with at most one control, on distinct qubits below `m`. -/
@[expose] def WellFormed (m : ℕ) : PhaseGateCode → Prop
  | (false, g) => g.WellFormed m
  | (true, _, t, cs) => cs.length ≤ 1 ∧ (t :: cs).Nodup ∧ ∀ i ∈ t :: cs, i < m

instance (m : ℕ) : DecidablePred (WellFormed m)
  | (false, g) => inferInstanceAs (Decidable (g.WellFormed m))
  | (true, _, t, cs) =>
    inferInstanceAs (Decidable (cs.length ≤ 1 ∧ (t :: cs).Nodup ∧ ∀ i ∈ t :: cs, i < m))

/-- **Exactly the well-formed codes denote gates.** -/
theorem isSome_toPlacedGate?_iff {c : PhaseGateCode} :
    (toPlacedGate? m c).isSome ↔ c.WellFormed m := by
  match c with
  | (false, g) => exact GateCode.isSome_toPlacedGate?_iff
  | (true, inv, t, []) => by_cases h : t < m <;> simp [toPlacedGate?, WellFormed, h]
  | (true, inv, t, [c]) =>
    simp only [toPlacedGate?]
    split_ifs with h <;> simp only [Option.isSome_some, Option.isSome_none] <;>
      simp only [WellFormed, List.length_cons, List.length_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, List.nodup_nil, forall_eq_or_imp, true_iff, false_iff,
        Bool.false_eq_true] <;> grind
  | (true, inv, t, _ :: _ :: _) => simp [toPlacedGate?, WellFormed]

/-- **A well-formed phase gate code denotes a controlled phase gate** on qubits `e` whose
conjunction is the one read by the classical gate code with the controls `t :: cs`, on a register
with one more qubit. -/
theorem exists_toPlacedGate?_eq_ctrlPhase {inv : Bool} {t : ℕ} {cs : List ℕ}
    (hc : WellFormed m (true, inv, t, cs)) :
    ∃ (k : ℕ) (e : Fin k ↪ Fin m),
      toPlacedGate? m (true, inv, t, cs) = some (PlacedGate.ctrlPhase inv e) ∧
      ∀ w : Fin (m + 1) → Bool, ((t :: cs).all fun c => (List.ofFn w).getD c false) =
        decide (∀ i, Fin.init w (e i) = true) := by
  have hread (w : Fin (m + 1) → Bool) {c : ℕ} (hc : c < m) :
      (List.ofFn w).getD c false = Fin.init w ⟨c, hc⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [Nat.lt_succ_of_lt hc, Fin.init]
  obtain ⟨hlen, hnd, hlt⟩ := hc
  match cs, hlen, hnd, hlt with
  | [], _, _, hlt =>
    have ht : t < m := hlt t List.mem_cons_self
    refine ⟨1, ⟨![⟨t, ht⟩], fun i j _ => Subsingleton.elim i j⟩, by simp [toPlacedGate?, ht],
      fun w => ?_⟩
    rw [List.all_cons, List.all_nil, Bool.and_true, hread w ht]
    simp only [Fin.forall_fin_one]
    change Fin.init w ⟨t, ht⟩ = decide (Fin.init w ⟨t, ht⟩ = true)
    simp
  | [c], _, hnd, hlt =>
    have ht : t < m := hlt t (by simp)
    have hc : c < m := hlt c (by simp)
    have hct : c ≠ t := fun h => by simp [h] at hnd
    have h : c < m ∧ t < m ∧ c ≠ t := ⟨hc, ht, hct⟩
    refine ⟨2, ⟨![⟨c, h.1⟩, ⟨t, h.2.1⟩], ?_⟩, ?_, fun w => ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | (simp [Fin.ext_iff] at hij; omega)
    · simp only [toPlacedGate?]
      rw [dite_eq_left h]
    · rw [List.all_cons, List.all_cons, List.all_nil, Bool.and_true, hread w ht, hread w hc]
      simp only [Fin.forall_fin_two]
      change _ = decide (Fin.init w ⟨c, hc⟩ = true ∧ Fin.init w ⟨t, ht⟩ = true)
      cases Fin.init w ⟨t, ht⟩ <;> cases Fin.init w ⟨c, hc⟩ <;> simp
  | _ :: _ :: _, hlen, _, _ => simp at hlen

/-- The classical gate code that flips the encoding qubit `m` under the controls `t :: cs` of a
well-formed phase gate code is well formed on `m + 1` qubits. -/
theorem wellFormed_ctrlCode {inv : Bool} {t : ℕ} {cs : List ℕ}
    (hc : WellFormed m (true, inv, t, cs)) : GateCode.WellFormed (m + 1) (false, m, t :: cs) := by
  obtain ⟨hlen, hnd, hlt⟩ := hc
  refine ⟨by simpa using hlen, List.nodup_cons.mpr ⟨fun h => Nat.lt_irrefl m (hlt m h), hnd⟩,
    fun i hi => ?_⟩
  rcases List.mem_cons.mp hi with rfl | hi
  · omega
  · have := hlt i hi
    omega

end PhaseGateCode

/-- The circuit on `m` qubits denoted by a list of gate codes with phase gates, applied first to
last. Codes that are not well formed are skipped. -/
@[expose] noncomputable def Circuit.ofPhaseCodes (m : ℕ) (gs : List PhaseGateCode) : Circuit m :=
  gs.filterMap (PhaseGateCode.toPlacedGate? m)

theorem Circuit.ofPhaseCodes_cons (c : PhaseGateCode) (gs : List PhaseGateCode) :
    Circuit.ofPhaseCodes m (c :: gs) = Circuit.ofPhaseCodes m [c] ++ Circuit.ofPhaseCodes m gs :=
  List.filterMap_append (l := [c]) (l' := gs)

namespace PhaseGateCode

/-- The probability that the final measurement of the circuit with phase gate codes `gs` on `m`
qubits, started in `|x 0^{m - n}⟩`, finds every qubit of `S` in state `1`. -/
noncomputable def onesProb (m : ℕ) (gs : List PhaseGateCode) (S : List ℕ) (x : List Bool) : ℝ :=
  measureProb (Circuit.run (Circuit.ofPhaseCodes m gs) (inputState m x)) (onesAt m S)

/-- The acceptance probability of the circuit with phase gate codes `gs` on `m` qubits on input
`x`: the final measurement finds qubit `0` in state `1`. -/
noncomputable def acceptProb (m : ℕ) (gs : List PhaseGateCode) (x : List Bool) : ℝ :=
  measureProb (Circuit.run (Circuit.ofPhaseCodes m gs) (inputState m x)) (accepting m)

theorem acceptProb_eq_onesProb (m : ℕ) (gs : List PhaseGateCode) (x : List Bool) :
    acceptProb m gs x = onesProb m gs [0] x := by
  unfold acceptProb onesProb accepting
  rfl

/-! ### The real translation -/

/-- The four Hadamard and classical gate codes that simulate a controlled phase gate on the qubits
`qs` (for `inv`, its inverse) with the encoding qubit `r`: the gate acts on the encoding qubit as
`J = [[0, -1], [1, 0]] = X Z` controlled by `qs`, with `Z = H X H`, and its inverse as
`J⁻¹ = Z X`. -/
@[expose] def phaseCodes (r : ℕ) (inv : Bool) (qs : List ℕ) : List GateCode :=
  if inv then [(false, r, qs), (true, r, []), (false, r, qs), (true, r, [])]
  else [(true, r, []), (false, r, qs), (true, r, []), (false, r, qs)]

/-- **The real translation of a gate code with phase gates**, with the encoding qubit `r`: a gate
code is kept, and a controlled phase gate on `t :: cs` becomes four Hadamard and CNOT or Toffoli
gate codes (`phaseCodes`). -/
@[expose] def realCodes (r : ℕ) (c : PhaseGateCode) : List GateCode :=
  if c.1 then phaseCodes r c.2.1 (c.2.2.1 :: c.2.2.2) else [c.2]

/-- The real translation of a list of gate codes with phase gates, with the encoding qubit `r`. -/
@[expose] def toRealCodes (r : ℕ) (gs : List PhaseGateCode) : List GateCode :=
  gs.flatMap fun c => realCodes r c

/-- The real translation has at most four gate codes per gate code. -/
theorem length_toRealCodes_le (r : ℕ) (gs : List PhaseGateCode) :
    (toRealCodes r gs).length ≤ 4 * gs.length := by
  induction gs with
  | nil => simp [toRealCodes]
  | cons c gs ih =>
    simp only [toRealCodes, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : (realCodes r c).length ≤ 4 := by grind [realCodes, phaseCodes]
    omega

/-- **Four Hadamard and classical gates simulate a controlled phase gate** through the real
encoding: the phase gate on the qubits `e` is simulated by `phaseCodes m inv qs`, when the
controls `qs` of the classical gate read the conjunction of the qubits `e`. -/
theorem realSimulates_phaseCodes (inv : Bool) {k : ℕ} (e : Fin k ↪ Fin m) {qs : List ℕ}
    (hqs : GateCode.WellFormed (m + 1) (false, m, qs))
    (hall : ∀ w : Fin (m + 1) → Bool, (qs.all fun c => (List.ofFn w).getD c false) =
      decide (∀ i, Fin.init w (e i) = true)) :
    (Circuit.ofCodes (m + 1) (phaseCodes m inv qs)).RealSimulates
      [PlacedGate.ctrlPhase inv e] := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  set r : Fin (m + 1) := Fin.last m with hr
  have hrm : (⟨m, hm⟩ : Fin (m + 1)) = r := rfl
  -- the decoded Hadamard and classical gates
  obtain ⟨hR, hhR⟩ : ∃ p, GateCode.toPlacedGate? (m + 1) (true, m, []) = some p :=
    Option.isSome_iff_exists.mp (GateCode.isSome_toPlacedGate?_iff.mpr ⟨hm, rfl⟩)
  obtain ⟨cx, hcx⟩ : ∃ p, GateCode.toPlacedGate? (m + 1) (false, m, qs) = some p :=
    Option.isSome_iff_exists.mp (GateCode.isSome_toPlacedGate?_iff.mpr hqs)
  obtain ⟨s, hs, hH⟩ : ∃ s : ℂ, s * s = 1 / 2 ∧ ∀ w : Fin (m + 1) → Bool,
      hR.eval (ket w) = s • ket (Function.update w r false) +
        (if w r then -s else s) • ket (Function.update w r true) := by
    refine ⟨(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), ?_, fun w => ?_⟩
    · rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
      norm_num
    · rw [GateCode.eval_toPlacedGate_hadamard_ket hhR hm, Fintype.sum_bool]
      simp only [hrm]
      cases w r <;> simp <;> abel
  have hX (w : Fin (m + 1) → Bool) : cx.eval (ket w) =
      ket (Function.update w r (w r ^^ decide (∀ i, Fin.init w (e i) = true))) := by
    rw [GateCode.eval_toPlacedGate_ket hcx hm, hall]
    rfl
  have hinit (w : Fin (m + 1) → Bool) (c : Bool) :
      Fin.init (Function.update w r c) = Fin.init w :=
    Fin.init_update_last ..
  have hdecode : Circuit.ofCodes (m + 1) (phaseCodes m inv qs) =
      if inv then [cx, hR, cx, hR] else [hR, cx, hR, cx] := by
    cases inv <;> simp [phaseCodes, Circuit.ofCodes, hhR, hcx]
  refine Circuit.realSimulates_of_matrix fun z z' => ?_
  rw [← Circuit.eval_ket_apply, hdecode]
  simp only [Circuit.matrix_cons, Circuit.matrix_nil, one_mul, PlacedGate.ctrlPhase_matrix_apply]
  have heq (w : Fin (m + 1) → Bool) (c : Bool) :
      z = Function.update w r c ↔ Fin.init z = Fin.init w ∧ z r = c := by
    rw [← Fin.snoc_init_self (Function.update w r c), eq_snoc_iff, Fin.init_update_last,
      Function.update_self]
  -- expand the four gates on `|z'⟩`, case by case on the controls and the encoding bit
  cases inv <;> by_cases hA : ∀ i, Fin.init z' (e i) = true <;> cases hzr : z' r <;>
    simp only [↓reduceIte, Bool.cond_true, Bool.cond_false, Bool.false_eq_true, Circuit.eval_cons,
      Circuit.eval_nil, hH, hX, hinit, hA, implies_true, decide_true, decide_false, map_add,
      map_smul,
      Function.update_self, Function.update_idem, hzr, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, ket_apply, smul_eq_mul, heq, smul_add, smul_smul] <;>
    -- compare the entry with the real block of the phase gate's entry
    by_cases hp : Fin.init z = Fin.init z' <;> cases z r <;>
    simp only [hp, true_and, false_and, ite_false, ite_true, Bool.false_eq_true,
      realEntry_false_false, realEntry_true_true, realEntry_true_false, realEntry_false_true,
      mul_zero, mul_one, add_zero, zero_add, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im] <;>
    push_cast <;> (try simp only [mul_neg, neg_mul, neg_neg, hs]) <;> norm_num

/-- The real translation of well-formed codes is well formed on one more qubit. -/
theorem wellFormed_toRealCodes {gs : List PhaseGateCode} (hgs : ∀ c ∈ gs, c.WellFormed m) :
    ∀ g ∈ toRealCodes m gs, g.WellFormed (m + 1) := by
  intro g hg
  obtain ⟨c, hc, hg⟩ := List.mem_flatMap.mp hg
  have hwf := hgs c hc
  match c, hwf, hg with
  | (false, g'), hwf, hg =>
    rw [show realCodes m (false, g') = [g'] from rfl, List.mem_singleton] at hg
    subst hg
    simpa using GateCode.WellFormed.shift (o := 0) (N := m + 1) (by omega) hwf
  | (true, inv, t, cs), hwf, hg =>
    have hH : GateCode.WellFormed (m + 1) (true, m, []) := ⟨by omega, rfl⟩
    have hX := wellFormed_ctrlCode hwf
    simp only [realCodes, phaseCodes] at hg
    cases inv <;> simp only [ite_true, ite_false, Bool.false_eq_true, List.mem_cons,
      List.not_mem_nil, or_false] at hg <;> rcases hg with rfl | rfl | rfl | rfl <;> assumption

/-- **The real translation simulates the circuit**: through the real encoding, with the encoding
qubit `m`, the translation of well-formed codes on `m` qubits simulates the circuit they denote. -/
theorem realSimulates_toRealCodes {gs : List PhaseGateCode} (hgs : ∀ c ∈ gs, c.WellFormed m) :
    (Circuit.ofCodes (m + 1) (toRealCodes m gs)).RealSimulates (Circuit.ofPhaseCodes m gs) := by
  induction gs with
  | nil => exact Circuit.RealSimulates.nil
  | cons c gs ih =>
    rw [toRealCodes, List.flatMap_cons, Circuit.ofCodes_append, Circuit.ofPhaseCodes_cons]
    refine Circuit.RealSimulates.append ?_ (ih fun c' hc' => hgs c' (List.mem_cons_of_mem _ hc'))
    have hc := hgs c List.mem_cons_self
    match c, hc with
    | (false, g), hc => exact GateCode.realSimulates_ofCodes hc
    | (true, inv, t, cs), hc =>
      obtain ⟨k, e, he, hall⟩ := exists_toPlacedGate?_eq_ctrlPhase hc
      have hdec : Circuit.ofPhaseCodes m [(true, inv, t, cs)] = [PlacedGate.ctrlPhase inv e] := by
        simp [Circuit.ofPhaseCodes, he]
      rw [hdec]
      exact realSimulates_phaseCodes inv e (wellFormed_ctrlCode hc) hall

/-- The input `x` on `m + 1` qubits is the input on `m` qubits followed by a zero, when `x` fits
into `m` qubits. -/
theorem _root_.Cslib.Quantum.inputState_succ {x : List Bool} (hx : x.length ≤ m) :
    inputState (m + 1) x = Fin.snoc (inputState m x) false := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [inputState, List.getElem?_eq_none_iff.mpr hx]
  · simp [inputState]

/-- The outcomes of `m + 1` qubits in which the qubits `S` below `m` read one are those whose
first `m` bits do. -/
theorem _root_.Cslib.Quantum.onesAt_succ {S : List ℕ} (hS : ∀ j ∈ S, j < m) :
    onesAt (m + 1) S = univ.filter fun z : Fin (m + 1) → Bool => Fin.init z ∈ onesAt m S := by
  ext z
  simp only [onesAt, mem_filter, mem_univ, true_and]
  exact forall₂_congr fun j hj =>
    ⟨fun ⟨_, h⟩ => ⟨hS j hj, h⟩, fun ⟨_, h⟩ => ⟨by have := hS j hj; omega, h⟩⟩

/-- **The real translation measures the original qubits as the circuit does**: for well-formed
codes on `m` qubits, an input that fits into them, and measured qubits below `m`, the real
translation on `m + 1` qubits finds the qubits `S` all one with the same probability. -/
theorem onesProb_toRealCodes {gs : List PhaseGateCode} (hgs : ∀ c ∈ gs, c.WellFormed m)
    {S : List ℕ} (hS : ∀ j ∈ S, j < m) {x : List Bool} (hx : x.length ≤ m) :
    Quantum.onesProb (m + 1) (toRealCodes m gs) S x = onesProb m gs S x := by
  rw [Quantum.onesProb, onesProb, inputState_succ hx,
    (realSimulates_toRealCodes hgs).run_snoc_false, onesAt_succ hS, measureProb_realEncode]

/-- **The real translation accepts as the circuit does.** -/
theorem acceptProb_toRealCodes {gs : List PhaseGateCode} (hgs : ∀ c ∈ gs, c.WellFormed m)
    (hm : 0 < m) {x : List Bool} (hx : x.length ≤ m) :
    Quantum.acceptProb (m + 1) (toRealCodes m gs) x = acceptProb m gs x := by
  rw [Quantum.acceptProb_eq_onesProb, acceptProb_eq_onesProb]
  exact onesProb_toRealCodes hgs (by simpa using hm) hx

/-- The real translation is computed in polynomial time. -/
theorem computableInPolyTime_toRealCodes {γ : Type} {enc : γ ↪ List Bool} {r : γ → ℕ}
    {gs : γ → List PhaseGateCode} (hr : ComputableInPolyTime r enc encUnary)
    (hgs : ComputableInPolyTime gs enc (encList (encPair encBool encGateCode))) :
    ComputableInPolyTime (fun c => toRealCodes (r c) (gs c)) enc (encList encGateCode) := by
  simp only [toRealCodes, realCodes, phaseCodes]
  fun_prop

end PhaseGateCode

/-- The circuit of gate codes without phase gates, read as gate codes with phase gates. -/
theorem Circuit.ofPhaseCodes_map (gs : List GateCode) :
    Circuit.ofPhaseCodes m (gs.map fun g => (false, g)) = Circuit.ofCodes m gs := by
  simp only [Circuit.ofPhaseCodes, Circuit.ofCodes, List.filterMap_map]
  rfl

/-! ### Uniform families with phase gates -/

/-- The encoding of gate codes with phase gates `(p, g)`: the phase flag, then the gate code `g`
(`Cslib.Quantum.encGateCode`). -/
abbrev encPhaseGateCode : PhaseGateCode ↪ List Bool := encPair encBool encGateCode

/-- A **polynomial-time uniform family of quantum circuits with phase gates**: as
`Cslib.Quantum.UniformCircuitFamily`, over the Hadamard, NOT, CNOT and Toffoli gates and the phase
gates `S`, `Λ(S)` and their inverses. On inputs of length `n` it uses a register of `width n`
qubits, at least `n` and at least one, and the well-formed codes `gates n`; both are computed from
`n` in unary in polynomial time. -/
structure UniformPhaseCircuitFamily where
  /-- The number of qubits used on inputs of length `n`. -/
  width : ℕ → ℕ
  /-- The gate codes of the circuit used on inputs of length `n`, applied first to last. -/
  gates : ℕ → List PhaseGateCode
  computableInPolyTime_width : ComputableInPolyTime width encUnary encUnary
  computableInPolyTime_gates : ComputableInPolyTime gates encUnary (encList encPhaseGateCode)
  le_width : ∀ n, n ≤ width n
  width_pos : ∀ n, 0 < width n
  wellFormed : ∀ n, ∀ g ∈ gates n, g.WellFormed (width n)

namespace UniformPhaseCircuitFamily

/-- The **acceptance probability** of the family on the input word `x`: its circuit for inputs of
length `|x|`, started in `|x 0^{m - |x|}⟩`, ends with qubit `0` measured in state `1`. -/
noncomputable def acceptProb (F : UniformPhaseCircuitFamily) (x : List Bool) : ℝ :=
  PhaseGateCode.acceptProb (F.width x.length) (F.gates x.length) x

/-- **The real simulation of a family with phase gates**: one more qubit, the encoding qubit, and
each controlled phase gate replaced by four Hadamard and CNOT or Toffoli gates
(`Cslib.Quantum.PhaseGateCode.realCodes`). -/
@[expose] def realify (F : UniformPhaseCircuitFamily) : UniformCircuitFamily where
  width n := F.width n + 1
  gates n := PhaseGateCode.toRealCodes (F.width n) (F.gates n)
  computableInPolyTime_width := by
    have := F.computableInPolyTime_width
    fun_prop
  computableInPolyTime_gates := PhaseGateCode.computableInPolyTime_toRealCodes
    F.computableInPolyTime_width F.computableInPolyTime_gates
  le_width n := Nat.le_succ_of_le (F.le_width n)
  width_pos n := Nat.succ_pos _
  wellFormed n := PhaseGateCode.wellFormed_toRealCodes (F.wellFormed n)

/-- **The real simulation accepts as the family does**, on every input. -/
@[simp] theorem acceptProb_realify (F : UniformPhaseCircuitFamily) (x : List Bool) :
    F.realify.acceptProb x = F.acceptProb x :=
  PhaseGateCode.acceptProb_toRealCodes (F.wellFormed _) (F.width_pos _) (F.le_width _)

/-- The circuits of the real simulation have at most four times as many gates. -/
theorem length_realify_gates_le (F : UniformPhaseCircuitFamily) (n : ℕ) :
    (F.realify.gates n).length ≤ 4 * (F.gates n).length :=
  PhaseGateCode.length_toRealCodes_le _ _

end UniformPhaseCircuitFamily

namespace UniformCircuitFamily

/-- A family over the Hadamard, NOT, CNOT and Toffoli gates, as a family with phase gates that uses
none. -/
@[expose] def toPhaseFamily (F : UniformCircuitFamily) : UniformPhaseCircuitFamily where
  width := F.width
  gates n := (F.gates n).map fun g => (false, g)
  computableInPolyTime_width := F.computableInPolyTime_width
  computableInPolyTime_gates := by
    have := F.computableInPolyTime_gates
    fun_prop
  le_width := F.le_width
  width_pos := F.width_pos
  wellFormed n c hc := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hc
    exact F.wellFormed n g hg

@[simp] theorem acceptProb_toPhaseFamily (F : UniformCircuitFamily) (x : List Bool) :
    F.toPhaseFamily.acceptProb x = F.acceptProb x := by
  simp only [UniformPhaseCircuitFamily.acceptProb, PhaseGateCode.acceptProb, toPhaseFamily,
    Circuit.ofPhaseCodes_map]
  rfl

end UniformCircuitFamily

end Cslib.Quantum
