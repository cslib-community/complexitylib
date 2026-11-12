/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.QMA
public import CslibFrontier.Computability.Complexity.Classes.BQP.Classical
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.OfFnGetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD

/-!
# `NP ⊆ QMA`

Every problem in `NP` has a quantum verifier with perfect completeness and soundness `0`
(`Cslib.Complexity.PromiseNP_subset_PromiseQMA`), so `NP ⊆ QMA`
(`Cslib.Complexity.NP_subset_QMA`); [Watrous][Watrous2008], Section V.2, calls this containment
trivial.

The verifier (`Cslib.Quantum.UniformVerifierFamily.ofNP`) is built from a uniform family `F` of
circuits that computes the NP relation on the words `frame x ++ w`, the pair encoding of an instance
and a certificate (`Cslib.Complexity.exists_uniformCircuitFamily`). On an input `x` of length `n`
and a witness of `p(n)` qubits, classical gates write `frame x ++ z` on a fresh block of qubits for
each basis witness `z` (`Cslib.Quantum.NPVerifier.frameCodes`), `F` runs on that block, and three
CNOT gates swap its answer into qubit `0`. The circuit is classical outside `F`, so on a basis
witness `|z⟩` it accepts exactly as `F` does on `frame x ++ z`
(`Cslib.Quantum.UniformVerifierFamily.acceptProb_ofNP_ket`). A yes-instance has a certificate
accepted with certainty; on a no-instance every basis witness is rejected with certainty, and then
so is every witness state (`Cslib.Quantum.UniformVerifierFamily.acceptProb_eq_zero_of_forall_ket`).

## Main definitions

* `Cslib.Quantum.UniformVerifierFamily.ofNP`: the quantum verifier of an NP relation.

## Main results

* `Cslib.Complexity.PromiseNP_subset_PromiseQMA`: `PromiseNP ⊆ QMA(1, 0)`.
* `Cslib.Complexity.NP_subset_QMA`: `NP ⊆ QMA`.

## References

* [J. Watrous, *Quantum computational complexity*][Watrous2008]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset Turing.MultiTapeTM GateCode

/-- The bits of `frame x`: a marker `true` before each bit of `x`, and `false` at the end. -/
private theorem getD_frame (x : List Bool) (k : ℕ) :
    (frame x).getD k false =
      if k < 2 * x.length then (if k % 2 = 0 then true else x.getD (k / 2) false) else false := by
  induction x generalizing k with
  | nil => cases k <;> simp [frame_nil]
  | cons b x ih =>
    rw [frame_cons]
    match k with
    | 0 => simp
    | 1 => simp; omega
    | k + 2 =>
      rw [List.getD_cons_succ, List.getD_cons_succ, ih, show (k + 2) / 2 = k / 2 + 1 by omega,
        List.getD_cons_succ, Nat.add_mod_right, List.length_cons]
      exact if_congr ⟨fun h => by omega, fun h => by omega⟩ rfl rfl

/-- The circuit `gs` on the block `o, …, o + w - 1` after classical codes `pre`, followed by
a swap of the block's first qubit into qubit `0`, accepts as `gs` does on the block's contents
after `pre`. -/
theorem measureProb_prep_shift_swap {N w o : ℕ} {pre gs : List GateCode}
    (hpre : IsClassical N pre) (hgs : ∀ g ∈ gs, WellFormed w g) (ho : 0 < o) (hw : 0 < w)
    (h : o + w ≤ N) (X : Fin N → Bool) :
    measureProb (Circuit.eval (Circuit.ofCodes N (pre ++ (gs.map (shift o) ++ swapCodes o)))
      (ket X)) (accepting N) =
      measureProb (Circuit.eval (Circuit.ofCodes w gs) (ket (classicalRun pre X ∘ blockEmb o h)))
        (accepting w) := by
  rw [Circuit.ofCodes_append, Circuit.ofCodes_append, Circuit.eval_append, Circuit.eval_append,
    Circuit.eval_ofCodes_ket hpre,
    Circuit.measureProb_eval_ofCodes (isClassical_swapCodes ho (by omega)),
    Circuit.ofCodes_map_shift h hgs]
  set X' := classicalRun pre X
  set C := Circuit.ofCodes w gs
  have hamp (Y : Fin N → Bool) : (Circuit.eval (C.mapWires (blockEmb o h)) (ket X')).ofLp Y =
      if AgreeOff (blockEmb o h) Y X' then
        (Circuit.eval C (ket (X' ∘ blockEmb o h))).ofLp (Y ∘ blockEmb o h) else 0 := by
    rw [Circuit.eval_ket_apply, Circuit.matrix_mapWires, Circuit.eval_ket_apply]
  have hacc (Y : Fin N → Bool) :
      classicalRun (swapCodes o) Y ∈ accepting N ↔ Y ∘ blockEmb o h ∈ accepting w := by
    rw [mem_accepting (by omega), mem_accepting hw, Function.comp_apply,
      ← readBit_fin (classicalRun _ Y)]
    change readBit _ 0 = true ↔ _
    rw [readBit_classicalRun_swapCodes ho (by omega), readBit_of_lt _ (by omega)]
    exact Iff.of_eq (congrArg (· = true) (congrArg Y (Fin.ext (by simp))))
  have hterm (Y : Fin N → Bool) :
      (if classicalRun (swapCodes o) Y ∈ accepting N then
        ‖(Circuit.eval (C.mapWires (blockEmb o h)) (ket X')).ofLp Y‖ ^ 2 else 0) =
      if AgreeOff (blockEmb o h) Y X' then
        (if Y ∘ blockEmb o h ∈ accepting w then
          ‖(Circuit.eval C (ket (X' ∘ blockEmb o h))).ofLp (Y ∘ blockEmb o h)‖ ^ 2 else 0)
      else 0 := by
    rw [if_congr (hacc Y) rfl rfl, hamp]
    split_ifs <;> simp
  simp only [hterm]
  rw [sum_agreeOff_comp (blockEmb o h) X' fun z => if z ∈ accepting w then
    ‖(Circuit.eval C (ket (X' ∘ blockEmb o h))).ofLp z‖ ^ 2 else 0, measureProb, ← sum_filter,
    filter_mem_eq_inter, univ_inter]

/-! ### The verifier of an NP relation -/

namespace NPVerifier

/-- Classical codes writing `frame x ++ z` on the block of qubits from `o` on, for an input `x` of
length `n` on qubits `0, …, n - 1` and a basis witness `z` of length `p` on qubits
`n, …, n + p - 1`: NOT gates set the frame's markers, and CNOT gates copy the bits. -/
def frameCodes (n p o : ℕ) : List GateCode :=
  (List.range n).flatMap (fun i => [(false, o + 2 * i, []), (false, o + 2 * i + 1, [i])]) ++
    (List.range p).map fun j => (false, o + 2 * n + 1 + j, [n + j])

theorem mem_frameCodes {n p o : ℕ} {g : GateCode} :
    g ∈ frameCodes n p o ↔ (∃ i < n, g = (false, o + 2 * i, []) ∨
      g = (false, o + 2 * i + 1, [i])) ∨ ∃ j < p, g = (false, o + 2 * n + 1 + j, [n + j]) := by
  simp only [frameCodes, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, h⟩
    · exact Or.inr ⟨j, hj, rfl⟩
  · rintro (⟨i, hi, h⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨i, hi, h⟩
    · exact Or.inr ⟨j, hj, rfl⟩

theorem nodup_frameCodes (n p o : ℕ) : ((frameCodes n p o).map fun g => g.2.1).Nodup := by
  rw [frameCodes, List.map_append, List.map_flatMap, List.map_map]
  simp only [List.map_cons, List.map_nil, Function.comp_def]
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · refine List.nodup_flatMap.mpr ⟨fun i _ => by simp, ?_⟩
    refine (List.nodup_range).pairwise_of_forall_ne fun i _ j _ hij => ?_
    simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false]
    omega
  · exact (List.nodup_range).map fun i j h => by simpa using h
  · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map]
    rintro _ ⟨i, hi, rfl | rfl⟩ _ ⟨j, hj, h⟩ <;> omega

variable {n p o M : ℕ}

theorem isClassical_frameCodes (h : o + 2 * n + 1 + p ≤ M) (ho : n + p ≤ o) :
    IsClassical M (frameCodes n p o) := by
  intro g hg
  rcases mem_frameCodes.mp hg with ⟨i, hi, rfl | rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨rfl, by simp, by simp, by simp; omega⟩
  · exact ⟨rfl, by simp, by simp; omega, by simp; omega⟩
  · exact ⟨rfl, by simp, by simp; omega, by simp; omega⟩

/-- **The classical codes write `frame x ++ z`** on the block from `o` on. -/
theorem readBit_classicalRun_frameCodes (h : o + 2 * n + 1 + p ≤ M) (ho : n + p ≤ o)
    {x : List Bool} (hx : x.length = n) (z : Fin p → Bool) (k : ℕ) :
    readBit (classicalRun (frameCodes n p o) (inputState M (x ++ List.ofFn z))) (o + k) =
      (frame x ++ List.ofFn z).getD k false := by
  set X := inputState M (x ++ List.ofFn z)
  have hX (q : ℕ) : readBit X q = (x ++ List.ofFn z).getD q false := by
    by_cases hq : q < M
    · rw [readBit_of_lt _ hq]; rfl
    · rw [readBit_of_le _ (not_lt.mp hq), List.getD_eq_default _ _ (by simp; omega)]
  have hXo (k : ℕ) : readBit X (o + k) = false := by
    rw [hX, List.getD_eq_default _ _ (by simp; omega)]
  have hmem {g : GateCode} (hg : g ∈ frameCodes n p o) :
      readBit (classicalRun (frameCodes n p o) X) g.2.1 =
        (readBit X g.2.1 ^^ g.2.2.all (readBit X)) :=
    readBit_classicalRun_of_mem (fun g hg => by
        rcases mem_frameCodes.mp hg with ⟨i, hi, rfl | rfl⟩ | ⟨j, hj, rfl⟩ <;> simp <;> omega)
      (nodup_frameCodes n p o) (fun g hg g' hg' => by
        rcases mem_frameCodes.mp hg with ⟨i, hi, rfl | rfl⟩ | ⟨j, hj, rfl⟩ <;>
        rcases mem_frameCodes.mp hg' with ⟨i', hi', rfl | rfl⟩ | ⟨j', hj', rfl⟩ <;> simp <;> omega)
      X hg
  have hfr (k : ℕ) : (frame x ++ List.ofFn z).getD k false =
      if k < 2 * n then (if k % 2 = 0 then true else x.getD (k / 2) false)
      else if k = 2 * n then false
      else (List.ofFn z).getD (k - (2 * n + 1)) false := by
    by_cases hk : k < 2 * n + 1
    · rw [List.getD_append _ _ _ _ (by simp [length_frame]; omega), getD_frame, hx]
      by_cases hk' : k < 2 * n
      · simp [hk']
      · simp [show k = 2 * n by omega]
    · rw [List.getD_append_right _ _ _ _ (by simp [length_frame]; omega), length_frame, hx,
        ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hfr]
  by_cases hk : k < 2 * n
  · rw [ite_eq_left hk]
    by_cases hpar : k % 2 = 0
    · have hg : ((false, o + 2 * (k / 2), []) : GateCode) ∈ frameCodes n p o :=
        mem_frameCodes.mpr (Or.inl ⟨k / 2, by omega, Or.inl rfl⟩)
      have := hmem hg
      simp only [List.all_nil, Bool.xor_true] at this
      rw [show o + 2 * (k / 2) = o + k by omega, hXo] at this
      rw [this, ite_eq_left hpar]; rfl
    · have hg : ((false, o + 2 * (k / 2) + 1, [k / 2]) : GateCode) ∈ frameCodes n p o :=
        mem_frameCodes.mpr (Or.inl ⟨k / 2, by omega, Or.inr rfl⟩)
      have := hmem hg
      simp only [List.all_cons, List.all_nil, Bool.and_true] at this
      rw [show o + 2 * (k / 2) + 1 = o + k by omega, hXo, hX,
        List.getD_append _ _ _ _ (by omega)] at this
      rw [this, ite_eq_right hpar]; simp
  · rw [ite_eq_right hk]
    by_cases hk2 : k = 2 * n
    · rw [ite_eq_left hk2, readBit_classicalRun_of_forall_ne (fun g hg => ?_), hXo]
      rcases mem_frameCodes.mp hg with ⟨i, hi, rfl | rfl⟩ | ⟨j, hj, rfl⟩ <;> simp <;> omega
    · rw [ite_eq_right hk2]
      by_cases hkp : k < 2 * n + 1 + p
      · have hg : ((false, o + 2 * n + 1 + (k - (2 * n + 1)), [n + (k - (2 * n + 1))]) : GateCode)
            ∈ frameCodes n p o := mem_frameCodes.mpr (Or.inr ⟨k - (2 * n + 1), by omega, rfl⟩)
        have := hmem hg
        simp only [List.all_cons, List.all_nil, Bool.and_true] at this
        rw [show o + 2 * n + 1 + (k - (2 * n + 1)) = o + k by omega, hXo, hX,
          List.getD_append_right _ _ _ _ (by omega), hx,
          show n + (k - (2 * n + 1)) - n = k - (2 * n + 1) by omega] at this
        rw [this]; simp
      · rw [readBit_classicalRun_of_forall_ne (fun g hg => ?_), hXo,
          List.getD_eq_default _ _ (by simp; omega)]
        rcases mem_frameCodes.mp hg with ⟨i, hi, rfl | rfl⟩ | ⟨j, hj, rfl⟩ <;> simp <;> omega

theorem computableInPolyTime_frameCodes {γ : Type} {enc : γ ↪ List Bool} {n p o : γ → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hp : ComputableInPolyTime p enc encUnary)
    (ho : ComputableInPolyTime o enc encUnary) :
    ComputableInPolyTime (fun c => frameCodes (n c) (p c) (o c)) enc (encList encGateCode) := by
  unfold frameCodes
  fun_prop

/-- The register of the verifier for inputs of length `n`: the input, the witness, one spare qubit,
and the register of `F` for words of length `2 n + 1 + p(n)`. -/
def width (F : UniformCircuitFamily) (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  n + p.eval n + 1 + F.width (2 * n + 1 + p.eval n)

/-- The verifier's circuit: write `frame x ++ z` on the block from `n + p(n) + 1` on, run `F` there,
and swap the block's first qubit into qubit `0`. -/
def gates (F : UniformCircuitFamily) (p : Polynomial ℕ) (n : ℕ) : List GateCode :=
  frameCodes n (p.eval n) (n + p.eval n + 1) ++
    ((F.gates (2 * n + 1 + p.eval n)).map (shift (n + p.eval n + 1)) ++
      swapCodes (n + p.eval n + 1))

end NPVerifier

namespace UniformVerifierFamily

open NPVerifier

/-- **The quantum verifier of an NP relation**: for a uniform family `F` of circuits on the
words `frame x ++ w` (the pair encoding of `(x, w)`), the verifier reads a witness of `p(|x|)`
qubits, writes `frame x ++ z` for each basis witness `z` and runs `F`. -/
def ofNP (F : UniformCircuitFamily) (p : Polynomial ℕ) : UniformVerifierFamily where
  width := NPVerifier.width F p
  gates := NPVerifier.gates F p
  computableInPolyTime_width := by
    have := F.computableInPolyTime_width
    unfold NPVerifier.width
    fun_prop
  computableInPolyTime_gates := by
    have hF := F.computableInPolyTime_gates
    have hshift (o : ℕ) : shift o = fun g => (g.1, g.2.1 + o, g.2.2.map (· + o)) := rfl
    have hfc := computableInPolyTime_frameCodes (enc := encUnary) (n := fun n => n)
      (p := fun n => p.eval n) (o := fun n => n + p.eval n + 1) (by fun_prop) (by fun_prop)
      (by fun_prop)
    change ComputableInPolyTime (fun n => NPVerifier.gates F p n) encUnary (encList encGateCode)
    simp only [NPVerifier.gates, hshift, swapCodes]
    fun_prop
  le_width n := by unfold NPVerifier.width; omega
  width_pos n := by unfold NPVerifier.width; omega
  wellFormed n g hg := by
    have hw := F.le_width (2 * n + 1 + p.eval n)
    have hw0 := F.width_pos (2 * n + 1 + p.eval n)
    rcases List.mem_append.mp hg with hg | hg
    · exact (isClassical_frameCodes (M := NPVerifier.width F p n)
        (by unfold NPVerifier.width; omega) (by omega) g hg).2
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hg
      exact (F.wellFormed _ g hg').shift (by unfold NPVerifier.width; omega)
    · exact (isClassical_swapCodes (by omega) (by unfold NPVerifier.width; omega) g hg).2
  witnessLength n := p.eval n
  computableInPolyTime_witnessLength := by fun_prop
  add_witnessLength_le n := by unfold NPVerifier.width; omega

/-- On a basis witness `|z⟩`, the verifier of an NP relation accepts as `F` does on
`frame x ++ z`. -/
theorem acceptProb_ofNP_ket (F : UniformCircuitFamily) (p : Polynomial ℕ) (x : List Bool)
    (z : Fin ((ofNP F p).witnessLength x.length) → Bool) :
    (ofNP F p).acceptProb x (ket z) = F.acceptProb (frame x ++ List.ofFn z) := by
  rw [acceptProb_ket]
  have hlen : (frame x ++ List.ofFn z).length = 2 * x.length + 1 + p.eval x.length := by
    rw [List.length_append, length_frame, List.length_ofFn]
    rfl
  have hw := F.le_width (2 * x.length + 1 + p.eval x.length)
  have hw0 := F.width_pos (2 * x.length + 1 + p.eval x.length)
  have hblock : x.length + p.eval x.length + 1 + F.width (2 * x.length + 1 + p.eval x.length) ≤
      NPVerifier.width F p x.length := le_rfl
  change measureProb (Circuit.eval (Circuit.ofCodes (NPVerifier.width F p x.length)
    (NPVerifier.gates F p x.length)) (ket (inputState _ (x ++ List.ofFn z))))
    (accepting (NPVerifier.width F p x.length)) = _
  rw [NPVerifier.gates, measureProb_prep_shift_swap (isClassical_frameCodes
    (by unfold NPVerifier.width; omega) (by omega)) (F.wellFormed _) (by omega) hw0 hblock]
  have hstate :
      classicalRun (frameCodes x.length (p.eval x.length) (x.length + p.eval x.length + 1))
      (inputState (NPVerifier.width F p x.length) (x ++ List.ofFn z)) ∘ blockEmb _ hblock =
      inputState _ (frame x ++ List.ofFn z) := by
    funext i
    rw [Function.comp_apply, ← readBit_fin (classicalRun _ _), blockEmb_apply_val,
      Nat.add_comm (i : ℕ)]
    exact readBit_classicalRun_frameCodes (M := NPVerifier.width F p x.length) (n := x.length)
      (p := p.eval x.length) (o := x.length + p.eval x.length + 1)
      (by unfold NPVerifier.width; omega) (by omega) rfl z i
  rw [hstate, UniformCircuitFamily.acceptProb, hlen]
  rfl

/-- The NP verifier's circuit, run on the word `x ++ w` for a proof `w` of the right length,
accepts as `F` does on `frame x ++ w`. -/
theorem measureProb_ofNP_inputState (F : UniformCircuitFamily) (p : Polynomial ℕ) (x w : List Bool)
    (hw : w.length = p.eval x.length) :
    measureProb (Circuit.eval (Circuit.ofCodes (NPVerifier.width F p x.length)
      (NPVerifier.gates F p x.length)) (ket (inputState _ (x ++ w))))
      (accepting (NPVerifier.width F p x.length)) = F.acceptProb (frame x ++ w) := by
  have hofFn : List.ofFn (fun i : Fin ((ofNP F p).witnessLength x.length) => w.getD i false) =
      w := List.ofFn_getD_eq_of_length false hw
  have := acceptProb_ofNP_ket F p x fun i => w.getD i false
  rw [acceptProb_ket, hofFn] at this
  exact this

end UniformVerifierFamily

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum Turing.MultiTapeTM PromiseProblem

variable {α : Type} {enc : α ↪ List Bool}

/-- **`PromiseNP ⊆ QMA(1, 0)`**: the verifier of an NP relation, run on a witness state, accepts a
basis state certificate with certainty, and when no certificate exists it accepts no witness
state. -/
theorem PromiseNP_subset_PromiseQMA : PromiseNP enc ⊆ PromiseQMA (fun _ => 1) (fun _ => 0) enc := by
  intro Q hQ
  obtain ⟨p, V, hV, hyes, hno⟩ := mem_PromiseNP_iff.mp hQ
  obtain ⟨F, hF⟩ := exists_uniformCircuitFamily hV
  have hket (a : α)
      (z : Fin ((UniformVerifierFamily.ofNP F p).witnessLength (enc a).length) → Bool) :
      (UniformVerifierFamily.ofNP F p).acceptProb (enc a) (ket z) =
        if V (a, List.ofFn z) then 1 else 0 := by
    rw [UniformVerifierFamily.acceptProb_ofNP_ket, ← hF (a, List.ofFn z)]
    rfl
  refine ⟨UniformVerifierFamily.ofNP F p, fun a => ⟨fun ha => ?_, fun ha ψ _ => ?_⟩⟩
  · obtain ⟨w, hw, hVw⟩ := hyes a ha
    have hofFn : List.ofFn (fun i : Fin ((UniformVerifierFamily.ofNP F p).witnessLength
        (enc a).length) => w.getD i false) = w := List.ofFn_getD_eq_of_length false hw
    refine ⟨ket fun i => w.getD i false, norm_ket _, ?_⟩
    rw [hket, hofFn, hVw]
    norm_num
  · rw [UniformVerifierFamily.acceptProb_eq_zero_of_forall_ket _ _ (fun z => ?_) ψ]
    have hlen : (List.ofFn z).length = p.eval (enc a).length := List.length_ofFn ..
    rw [hket, hno a ha _ hlen]
    norm_num

/-- **`NP ⊆ QMA`** [Watrous][Watrous2008], Section V.2. -/
theorem NP_subset_QMA : NP enc ⊆ QMA enc := fun A hA =>
  PromiseQMA_mono (fun _ => by norm_num) (fun _ => by norm_num)
    (PromiseNP_subset_PromiseQMA (ofSet_mem_PromiseNP.mpr hA))

end Cslib.Complexity
