/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Code
import Complexity.Foundations.Data.List.Lookup

/-!
# Amplitudes of Hadamard–Toffoli circuits as path sums

The gates of `Complexity/Computability/Circuit/Quantum/Code.lean` act on basis states either as
permutations (NOT, CNOT, Toffoli) or by branching into two basis states with amplitudes `±1/√2`
(Hadamard). Following one branch per Hadamard gate gives a *path*: a bit string of length `h`, the
number of Hadamard gates (`Cslib.Quantum.hadamardCount`). The classical simulation
`Cslib.Quantum.pathStep` follows a path on a register written as a bit string. It writes the next
path bit into the target of a Hadamard gate, flipping a sign when the old and new bits are both
one, and it applies classical gates directly. Every amplitude of the circuit is then a signed count
of paths divided by `√2^h` (`Cslib.Quantum.run_ofCodes_apply`):
`⟨y|C|x⟩ = (∑_π ±[π ends in y]) / √2^h`. This adapts the argument of Fortnow and Rogers
[Fortnow, Rogers][FortnowRogers1999], Lemma 3.2, from quantum Turing machines to circuits.

Squaring and summing over the accepting outcomes, the acceptance probability is a signed count of
*pairs* of paths that end in the same accepting register, divided by `2^h`
(`Cslib.Quantum.acceptProb_eq_acceptGap`). Both counts are integers computed from polynomial-time
simulations, which places `BQP` in the counting classes
(`Complexity/Computability/Complexity/Classes/BQP/Counting.lean`).

## Main definitions

* `Cslib.Quantum.pathStep`, `Cslib.Quantum.pathRun`: the path simulation.
* `Cslib.Quantum.hadamardCount`: the number of Hadamard gates.
* `Cslib.Quantum.pathTerm`, `Cslib.Quantum.pathGap`: the signed path count of an amplitude.
* `Cslib.Quantum.acceptTerm`, `Cslib.Quantum.acceptGap`: the signed count of pairs of paths of the
  acceptance probability.

## Main results

* `Cslib.Quantum.ofFn_inputState`: the input basis state is the input word padded with zeros.
* `Cslib.Quantum.run_ofCodes_apply`: amplitudes are path sums.
* `Cslib.Quantum.acceptProb_eq_acceptGap`: the acceptance probability is `acceptGap / 2^h`.

## References

* [L. Fortnow, J. Rogers, *Complexity limitations on quantum computation*][FortnowRogers1999]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset

variable {m : ℕ}

/-- The input basis state as a bit string: the input word padded with zeros. -/
theorem ofFn_inputState {x : List Bool} (hx : x.length ≤ m) :
    List.ofFn (inputState m x) = x ++ List.replicate (m - x.length) false := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_ofFn, inputState, List.getElem_append, List.getElem_replicate]
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h)]

/-! ### The path simulation -/

/-- One step of the path simulation. The state holds the register bits, the unread path bits and a
sign. A Hadamard gate on `t` writes the next path bit `c` into `t`, flipping the sign when the old
and new bits are both one; a classical gate flips `t` when all its controls are one. -/
def pathStep : List Bool × List Bool × Bool → GateCode → List Bool × List Bool × Bool
  | (s, π, σ), (true, t, _) =>
    (s.set t (π.headD false), π.tail, σ ^^ (s.getD t false && π.headD false))
  | (s, π, σ), (false, t, cs) =>
    (s.set t (s.getD t false ^^ cs.all fun c => s.getD c false), π, σ)

/-- The number of Hadamard gates in a list of gate codes. -/
def hadamardCount : List GateCode → ℕ
  | [] => 0
  | (true, _, _) :: gs => hadamardCount gs + 1
  | (false, _, _) :: gs => hadamardCount gs

@[simp] theorem hadamardCount_nil : hadamardCount [] = 0 := rfl

@[simp] theorem hadamardCount_cons_true (t : ℕ) (cs : List ℕ) (gs : List GateCode) :
    hadamardCount ((true, t, cs) :: gs) = hadamardCount gs + 1 := rfl

@[simp] theorem hadamardCount_cons_false (t : ℕ) (cs : List ℕ) (gs : List GateCode) :
    hadamardCount ((false, t, cs) :: gs) = hadamardCount gs := rfl

/-- The Hadamard gates are the codes flagged `true`. -/
theorem hadamardCount_eq_countP (gs : List GateCode) :
    hadamardCount gs = gs.countP fun g => g.1 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨_ | _, t, cs⟩ := g <;> simp [ih]

/-- The final register and sign of the simulation from the register `x` along the path `π`. -/
def pathRun (gs : List GateCode) (x π : List Bool) : List Bool × Bool :=
  match gs.foldl pathStep (x, π, false) with
  | (s, _, σ) => (s, σ)

/-- The signed contribution of the path `π` to the amplitude `⟨y|C|x⟩`: `±1` when the simulation
from `x` along `π` ends in `y`, with the sign it accumulates, and `0` otherwise. -/
def pathTerm (gs : List GateCode) (x y π : List Bool) : ℤ :=
  match pathRun gs x π with
  | (s, σ) => if s = y then (if σ then -1 else 1) else 0

/-- The amplitude gap: the sum of `pathTerm` over all paths of one bit per Hadamard gate. -/
def pathGap (gs : List GateCode) (x y : List Bool) : ℤ :=
  ∑ π : Fin (hadamardCount gs) → Bool, pathTerm gs x y (List.ofFn π)

/-- The signed contribution of a pair of paths to the acceptance probability: the product of
their signs when both end in the same register with qubit `0` equal to one, and `0` otherwise. -/
def acceptTerm (gs : List GateCode) (x π π' : List Bool) : ℤ :=
  match pathRun gs x π, pathRun gs x π' with
  | (s, σ), (s', σ') =>
    if s = s' ∧ s.headD false = true then (if σ ^^ σ' then -1 else 1) else 0

/-- The acceptance gap: the sum of `acceptTerm` over all pairs of paths. -/
def acceptGap (gs : List GateCode) (x : List Bool) : ℤ :=
  ∑ π : Fin (hadamardCount gs) → Bool, ∑ π' : Fin (hadamardCount gs) → Bool,
    acceptTerm gs x (List.ofFn π) (List.ofFn π')

/-- The sign `±1` of a Boolean, in `ℂ`. -/
private abbrev sgn (σ : Bool) : ℂ := if σ then -1 else 1

private theorem sgn_xor (σ τ : Bool) : sgn (σ ^^ τ) = sgn σ * sgn τ := by
  cases σ <;> cases τ <;> simp [sgn]

/-- The contribution of a path, for a simulation started with sign `σ`. -/
private def term (gs : List GateCode) (x y : List Bool) (σ : Bool) (π : List Bool) : ℤ :=
  if (gs.foldl pathStep (x, π, σ)).1 = y then
    (if (gs.foldl pathStep (x, π, σ)).2.2 then -1 else 1) else 0

private theorem pathRun_eq (gs : List GateCode) (x π : List Bool) :
    pathRun gs x π = ((gs.foldl pathStep (x, π, false)).1, (gs.foldl pathStep (x, π, false)).2.2) :=
  rfl

private theorem pathTerm_eq_term (gs : List GateCode) (x y π : List Bool) :
    pathTerm gs x y π = term gs x y false π :=
  rfl

/-- **Amplitudes are path sums** (generalized over the initial sign). -/
private theorem sgn_mul_run_ofCodes_apply (gs : List GateCode)
    (hgs : ∀ g ∈ gs, g.WellFormed m) (x y : Fin m → Bool) (σ : Bool) :
    sgn σ * (Circuit.run (Circuit.ofCodes m gs) x).ofLp y =
      (∑ π : Fin (hadamardCount gs) → Bool,
        (term gs (List.ofFn x) (List.ofFn y) σ (List.ofFn π) : ℂ)) *
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ hadamardCount gs := by
  induction gs generalizing x σ with
  | nil =>
    have hterm (π : List Bool) : term [] (List.ofFn x) (List.ofFn y) σ π =
        if x = y then (if σ then -1 else 1) else 0 := by
      by_cases h : x = y <;> simp [term, h]
    simp only [Circuit.ofCodes_nil, Circuit.run, Circuit.eval_nil, ket_apply, hterm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    simp only [hadamardCount_nil, pow_zero, one_smul, mul_one]
    by_cases h : x = y
    · subst h
      cases σ <;> simp [sgn]
    · simp [h, Ne.symm h]
  | cons g gs ih =>
    have hgs' : ∀ g ∈ gs, g.WellFormed m := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.mp
      (GateCode.isSome_toPlacedGate?_iff.mpr (hgs g List.mem_cons_self))
    have hofCodes : Circuit.ofCodes m (g :: gs) = pg :: Circuit.ofCodes m gs := by
      simp [Circuit.ofCodes, hpg]
    have hrun (z : Fin m → Bool) : Circuit.run (Circuit.ofCodes m (g :: gs)) z =
        Circuit.eval (Circuit.ofCodes m gs) (pg.eval (ket z)) := by
      rw [hofCodes, Circuit.run, Circuit.eval_cons]
    obtain ⟨h, t, cs⟩ := g
    cases h
    · -- a classical gate moves the basis state
      have ht : t < m := (hgs _ List.mem_cons_self).2.2 t List.mem_cons_self
      have hget : (List.ofFn x).getD t false = x ⟨t, ht⟩ := List.getD_ofFn_of_lt x ht false
      have hset (b : Bool) : (List.ofFn x).set t b = List.ofFn (Function.update x ⟨t, ht⟩ b) :=
        List.set_ofFn x ⟨t, ht⟩ b
      rw [hrun, GateCode.eval_toPlacedGate_ket hpg ht, ← Circuit.run, ih hgs']
      simp only [term, List.foldl_cons, pathStep, hget, hset]
      rfl
    · -- a Hadamard gate branches over the next path bit
      have ht : t < m := (hgs _ List.mem_cons_self).1
      have hcs : cs = [] := (hgs _ List.mem_cons_self).2
      subst hcs
      have hget : (List.ofFn x).getD t false = x ⟨t, ht⟩ := List.getD_ofFn_of_lt x ht false
      have hset (b : Bool) : (List.ofFn x).set t b = List.ofFn (Function.update x ⟨t, ht⟩ b) :=
        List.set_ofFn x ⟨t, ht⟩ b
      have hterm (c : Bool) (π' : Fin (hadamardCount gs) → Bool) :
          term ((true, t, []) :: gs) (List.ofFn x) (List.ofFn y) σ
            (List.ofFn (Fin.cons c π' : Fin (hadamardCount gs + 1) → Bool)) =
          term gs (List.ofFn (Function.update x ⟨t, ht⟩ c)) (List.ofFn y)
            (σ ^^ (x ⟨t, ht⟩ && c)) (List.ofFn π') := by
        simp only [term, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.foldl_cons, pathStep,
          List.headD_cons, List.tail_cons, hget, hset]
      rw [hrun, GateCode.eval_toPlacedGate_hadamard_ket hpg ht, map_sum, hadamardCount_cons_true,
        ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_mul,
        WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Fin.consEquiv_apply, hterm, map_smul, WithLp.ofLp_smul, Pi.smul_apply,
        smul_eq_mul]
      have hih := ih hgs' (Function.update x ⟨t, ht⟩ c) (σ ^^ (x ⟨t, ht⟩ && c))
      rw [Circuit.run, sgn_xor] at hih
      rw [pow_succ]
      simp only [sgn] at hih ⊢
      linear_combination (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * hih

/-- **Amplitudes are path sums**: for well-formed codes, the amplitude `⟨y|C|x⟩` of the decoded
circuit is the amplitude gap `pathGap` divided by `√2^h`, where `h` counts the Hadamard gates. -/
theorem run_ofCodes_apply (gs : List GateCode) (hgs : ∀ g ∈ gs, g.WellFormed m)
    (x y : Fin m → Bool) :
    (Circuit.run (Circuit.ofCodes m gs) x).ofLp y =
      (pathGap gs (List.ofFn x) (List.ofFn y) : ℂ) *
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ hadamardCount gs := by
  have h := sgn_mul_run_ofCodes_apply gs hgs x y false
  simp only [sgn, Bool.false_eq_true, ite_false, one_mul] at h
  rw [h, pathGap, Int.cast_sum]
  rfl

/-- The simulation keeps the register length. -/
private theorem length_foldl_pathStep (gs : List GateCode) (s π : List Bool) (σ : Bool) :
    (gs.foldl pathStep (s, π, σ)).1.length = s.length := by
  induction gs generalizing s π σ with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨_ | _, t, cs⟩ := g <;> simp only [List.foldl_cons, pathStep, ih, List.length_set]

private theorem pathTerm_eq (gs : List GateCode) (x y π : List Bool) :
    pathTerm gs x y π =
      if (pathRun gs x π).1 = y then (if (pathRun gs x π).2 then -1 else 1) else 0 :=
  rfl

private theorem acceptTerm_eq (gs : List GateCode) (x π π' : List Bool) :
    acceptTerm gs x π π' =
      if (pathRun gs x π).1 = (pathRun gs x π').1 ∧ (pathRun gs x π).1.headD false = true then
        (if (pathRun gs x π).2 ^^ (pathRun gs x π').2 then -1 else 1) else 0 :=
  rfl

/-- Summing the products of two path contributions over the accepting outcomes gives the
contribution of the pair. -/
private theorem sum_accepting_pathTerm_mul (hm : 0 < m) (gs : List GateCode) (x π π' : List Bool)
    (hx : x.length = m) :
    ∑ y ∈ accepting m, pathTerm gs x (List.ofFn y) π * pathTerm gs x (List.ofFn y) π' =
      acceptTerm gs x π π' := by
  have hs : (pathRun gs x π).1.length = m := (length_foldl_pathStep gs x π false).trans hx
  simp only [pathTerm_eq, acceptTerm_eq]
  generalize pathRun gs x π = r at hs ⊢
  generalize pathRun gs x π' = r'
  obtain ⟨s, σ⟩ := r
  obtain ⟨s', σ'⟩ := r'
  dsimp only at hs ⊢
  let y₀ : Fin m → Bool := fun i => s.getD i false
  have hs₀ : s = List.ofFn y₀ := by
    apply List.ext_getElem (by simp [hs])
    intro i h₁ h₂
    simp [y₀, List.getD_eq_getElem?_getD, h₁]
  have hiff (y : Fin m → Bool) : s = List.ofFn y ↔ y = y₀ := by
    rw [hs₀, List.ofFn_inj, eq_comm]
  simp only [hiff, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (accepting m) y₀]
  have hacc : y₀ ∈ accepting m ↔ s.headD false = true := by
    rw [mem_accepting hm]
    simp only [y₀]
    cases s with
    | nil => simp at hs; omega
    | cons b s => rfl
  by_cases h₀ : y₀ ∈ accepting m
  · simp only [h₀, ite_true, ← hs₀, hacc.mp h₀, and_true]
    by_cases hss : s = s'
    · subst hss
      cases σ <;> cases σ' <;> simp
    · simp [hss, Ne.symm hss]
  · simp only [h₀, ite_false, mt hacc.mpr h₀, Bool.false_eq_true, and_false]

/-- The squared amplitude gaps of the accepting outcomes sum to the acceptance gap. -/
private theorem sum_accepting_pathGap_sq (hm : 0 < m) (gs : List GateCode) (x : List Bool)
    (hx : x.length = m) :
    ∑ y ∈ accepting m, pathGap gs x (List.ofFn y) ^ 2 = acceptGap gs x := by
  simp only [pathGap, sq, Finset.sum_mul_sum, acceptGap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun π' _ => sum_accepting_pathTerm_mul hm gs x _ _ hx

/-- **The acceptance probability is a gap over `2^h`**: for well-formed codes on `m > 0` qubits,
the acceptance probability is `acceptGap` divided by `2^h`, where `h` counts the Hadamard
gates. -/
theorem acceptProb_eq_acceptGap (hm : 0 < m) (gs : List GateCode)
    (hgs : ∀ g ∈ gs, g.WellFormed m) (x : List Bool) :
    acceptProb m gs x =
      (acceptGap gs (List.ofFn (inputState m x)) : ℝ) / 2 ^ hadamardCount gs := by
  have hnorm (g : ℤ) :
      ‖(g : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ hadamardCount gs‖ ^ 2 =
        (g : ℝ) ^ 2 / 2 ^ hadamardCount gs := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg 2), Complex.norm_intCast, mul_pow, sq_abs, ← pow_mul,
      mul_comm (hadamardCount gs) 2, pow_mul, inv_pow, Real.sq_sqrt (by norm_num), inv_pow,
      div_eq_mul_inv]
  rw [acceptProb, measureProb]
  simp only [run_ofCodes_apply gs hgs, hnorm, ← Finset.sum_div]
  congr 1
  exact_mod_cast sum_accepting_pathGap_sq hm gs _ (by simp)

end Cslib.Quantum
