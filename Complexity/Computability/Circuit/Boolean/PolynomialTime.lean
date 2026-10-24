/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (redo of the withdrawn cslib PR #1101); blocked on the definitions of
-- `Complexity.P` (crei's `ComputableTidilyInPolyTime`, built on the merged #1126)

public import Complexity.Computability.Circuit.Boolean.BoundedError
public import Complexity.Computability.Circuit.Boolean.MachineSimulation
public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Classes.RP
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run

/-!
# P ⊆ P/poly and BPP ⊆ P/poly

A problem decided in polynomial time has circuits of polynomial size
[Arora and Barak, Theorem 6.6][AroraBarak09]: the machine deciding it writes `[true]` within
polynomially many steps exactly on the encoded members, and the inputs on which a machine does so
form a language in `P/poly` (`MachineSimulation.acceptedWithin_mem_PPoly`). With Adleman's theorem
(`PPoly.of_boundedError`), the same holds for problems decided with bounded error
[Arora and Barak, Theorem 7.14][AroraBarak09]: the verifier's circuits read `frame x ++ r`, whose
bits are bits of `x`, bits of `r` or constants (`frameWiring`), so they are circuits for a function
of `x ++ r` of the same size up to two gates.

## Main results

* `Cslib.Circuits.Boolean.PPoly.exists_of_polyTime`: the instances on which a Boolean function
  computable in polynomial time is true are the preimage of a language in `P/poly`.
* `Cslib.Circuits.Boolean.PPoly.exists_of_mem_P`: a problem in `P`, with any encoding of its
  instances, is the preimage of a language in `P/poly`.
* `Cslib.Circuits.Boolean.PPoly.of_mem_P`: `P ⊆ P/poly` for languages over `Bool`.
* `Cslib.Circuits.Boolean.PPoly.exists_of_mem_BPP`, `PPoly.exists_of_mem_RP`: the same for `BPP`
  and `RP`, with any encoding.
* `Cslib.Circuits.Boolean.PPoly.of_mem_BPP`, `PPoly.of_mem_RP`, `PPoly.of_mem_coRP`:
  `BPP, RP, coRP ⊆ P/poly` for languages over `Bool`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.5][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 9.3][Sipser2013]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing Turing.MultiTapeTM MachineSimulation

/-- The instances on which a Boolean function computable in polynomial time is true are the
preimage, under the encoding, of a language in `P/poly`. -/
theorem PPoly.exists_of_polyTime {α : Type*} {enc : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f enc encBool) :
    ∃ L ∈ PPoly, ∀ a, f a = true ↔ enc a ∈ L := by
  have hf := hf.tidy
  obtain ⟨t, s, ht, -, k, State, hfin, tm, htm⟩ := hf
  obtain ⟨c, d, ht⟩ := ht.exists_le
  have := Fintype.ofFinite State
  classical
  refine ⟨acceptedWithin tm fun n => c * (n + 1) ^ d, acceptedWithin_mem_PPoly tm (by fun_prop),
    fun a => ?_⟩
  obtain ⟨hhalt, hout⟩ := (htm a).runFrom_initCfg
  rw [mem_acceptedWithin_iff, MultiTapeTM.runFrom_eq_of_halt tm _ (ht a) hhalt, hout,
    encBool_apply]
  simp [OutView.ofList]

/-- **P ⊆ P/poly.** A problem in `P`, with any encoding `enc` of its instances, is the preimage
under `enc` of a language in `P/poly`. -/
theorem PPoly.exists_of_mem_P {α : Type*} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ Complexity.P enc) : ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨L, hL, h⟩ := PPoly.exists_of_polyTime hf
  exact ⟨L, hL, fun a => (hA a).trans (h a)⟩

/-- **P ⊆ P/poly** for languages over `Bool`, with words encoded as themselves. -/
theorem PPoly.of_mem_P {L : Language Bool} (hL : (L : Set (List Bool)) ∈ Complexity.P encBits) :
    L ∈ PPoly := by
  obtain ⟨L', hL', h⟩ := PPoly.exists_of_mem_P hL
  have : L = L' := Language.ext fun w => h w
  exact this ▸ hL'

/-! ### Randomised classes -/

/-- The substitution feeding a function of `2 n + 1 + P` variables with `frame x ++ r`, from the
variables `x ++ r`. -/
def frameWiring (n P : ℕ) (j : Fin (2 * n + 1 + P)) : Fin (n + P) ⊕ Bool :=
  if h : j.val < 2 * n then
    (if j.val % 2 = 0 then .inr true else .inl (Fin.castAdd P ⟨j.val / 2, by omega⟩))
  else if h' : j.val = 2 * n then .inr false
  else .inl (Fin.natAdd n ⟨j.val - (2 * n + 1), by have := j.isLt; omega⟩)

theorem ofFn_substitute_frameWiring {n P : ℕ} (x : Fin n → Bool) (r : Fin P → Bool) :
    List.ofFn (substitute (frameWiring n P) (Fin.append x r)) =
      frame (List.ofFn x) ++ List.ofFn r := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.length_ofFn] at h₁ ⊢
  by_cases hj : j < 2 * n + 1
  · rw [List.getElem_append_left (by simpa using hj), getElem_frame]
    simp only [substitute, frameWiring, List.length_ofFn]
    by_cases h : j < 2 * n
    · simp only [h, dite_true]
      split_ifs
      · simp [*]
      · simp only [Sum.elim_inl, List.getElem_ofFn, *]
        exact Fin.append_left x r ⟨j / 2, by omega⟩
    · obtain rfl : j = 2 * n := by omega
      simp
  · rw [List.getElem_append_right (by simpa using hj)]
    simp only [substitute, frameWiring, show ¬j < 2 * n by omega, dite_false,
      show j ≠ 2 * n by omega, length_frame, List.length_ofFn, List.getElem_ofFn, Sum.elim_inl]
    exact Fin.append_right x r ⟨j - (2 * n + 1), by omega⟩

/-- The function of `x ++ r` that tests `frame x ++ r ∈ L`. -/
noncomputable def framedSlice (L : Language Bool) (n P : ℕ) : BooleanFunction (n + P) :=
  fun y => L.slice (2 * n + 1 + P) (substitute (frameWiring n P) y)

private theorem framedSlice_append_eq_true {L : Language Bool} {n P : ℕ} (x : Fin n → Bool)
    (r : Fin P → Bool) :
    framedSlice L n P (Fin.append x r) = true ↔ frame (List.ofFn x) ++ List.ofFn r ∈ L := by
  rw [framedSlice, Language.slice_eq_true_iff, ofFn_substitute_frameWiring]

/-- Framing costs at most two gates. -/
private theorem polynomiallyBounded_complexity_framedSlice {L : Language Bool} (hL : L ∈ PPoly)
    {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    PolynomiallyBounded fun n => complexity interpretation (single (framedSlice L n (p n))) := by
  set q := fun N => complexity interpretation (single (L.slice N)) with hq
  have : PolynomiallyBounded q := hL
  exact PolynomiallyBounded.mono_of_le (g := fun n => q (2 * n + 1 + p n) + 2) (by fun_prop)
    fun n => complexity_substitute_le _ _

section Encoded

variable {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
  {L : Language Bool}

/-- The words of length `n` that encode an instance. -/
def encodes (enc : α ↪ List Bool) (n : ℕ) : Set (Fin n → Bool) := {x | ∃ a, enc a = List.ofFn x}

open scoped Classical in
/-- Whether the word `x` encodes a member of `A`. -/
noncomputable def encodesMember (enc : α ↪ List Bool) (A : Set α) (n : ℕ) : BooleanFunction n :=
  fun x => decide (∃ a ∈ A, enc a = List.ofFn x)

theorem encodesMember_eq_true_iff {A : Set α} {n : ℕ} {x : Fin n → Bool} {a : α}
    (ha : enc a = List.ofFn x) : encodesMember enc A n x = true ↔ a ∈ A := by
  rw [encodesMember, @decide_eq_true_iff _ (Classical.propDecidable _)]
  exact ⟨fun ⟨b, hb, hba⟩ => enc.injective (hba.trans ha.symm) ▸ hb, fun h => ⟨a, h, ha⟩⟩

/-- A language agreeing with `encodesMember enc A` on encoded words contains exactly the encodings
of the members of `A`. -/
theorem mem_iff_of_slice_eq_encodesMember {A : Set α}
    (h : ∀ n, ∀ x ∈ encodes enc n, L.slice n x = encodesMember enc A n x) (a : α) :
    a ∈ A ↔ enc a ∈ L := by
  have hx : List.ofFn (fun i : Fin (enc a).length => (enc a)[i]) = enc a := List.ofFn_getElem
  rw [← encodesMember_eq_true_iff hx.symm, ← h _ _ ⟨a, hx.symm⟩, Language.slice_eq_true_iff, hx]

/-- The verifier on an encoded instance, as the framed slice of the language deciding it. -/
theorem verifier_eq_true_iff (hVL : ∀ y, V y = true ↔ encPair enc encBits y ∈ L) {n : ℕ}
    {x : Fin n → Bool} {a : α} (ha : enc a = List.ofFn x) (r : List Bool) {P : ℕ}
    (r' : Fin P → Bool) (hr : r = List.ofFn r') :
    V (a, r) = true ↔ framedSlice L n P (Fin.append x r') = true := by
  rw [hVL, framedSlice_append_eq_true, encPair_apply, encBits_apply, ha, hr]

/-- **BPP ⊆ P/poly.** A problem in `BPP`, with any encoding `enc` of its instances, is the
preimage under `enc` of a language in `P/poly`. -/
theorem PPoly.exists_of_mem_BPP {A : Set α} (hA : A ∈ Complexity.BPP enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L := by
  obtain ⟨p, V, hV, hdec⟩ := hA
  obtain ⟨L', hL', hVL⟩ := PPoly.exists_of_polyTime hV
  obtain ⟨L, hL, hLg⟩ := PPoly.exists_of_boundedError (fun n => framedSlice L' n (p.eval n))
    (polynomiallyBounded_complexity_framedSlice hL' (by fun_prop)) (encodes enc)
    (encodesMember enc A) fun n x ⟨a, ha⟩ => by
      have h := hdec a
      rw [ha, List.length_ofFn] at h
      by_cases haA : a ∈ A
      · rw [(encodesMember_eq_true_iff ha).2 haA]
        exact (h.1 haA).trans_eq (congrArg (3 * ·) (congrArg Finset.card
          (Finset.filter_congr fun r _ => verifier_eq_true_iff hVL ha _ r rfl)))
      · rw [show encodesMember enc A n x = false from
          Bool.eq_false_iff.2 fun e => haA ((encodesMember_eq_true_iff ha).1 e)]
        refine (h.2 haA).trans_eq (congrArg (3 * ·) (congrArg Finset.card
          (Finset.filter_congr fun r _ => ?_)))
        rw [← Bool.not_eq_true, verifier_eq_true_iff hVL ha _ r rfl, Bool.not_eq_true]
  exact ⟨L, hL, mem_iff_of_slice_eq_encodesMember hLg⟩

/-- **RP ⊆ P/poly.** A problem in `RP`, with any encoding `enc` of its instances, is the preimage
under `enc` of a language in `P/poly`. -/
theorem PPoly.exists_of_mem_RP {A : Set α} (hA : A ∈ Complexity.RP enc) :
    ∃ L ∈ PPoly, ∀ a, a ∈ A ↔ enc a ∈ L := by
  obtain ⟨p, V, hV, hdec⟩ := hA
  obtain ⟨L', hL', hVL⟩ := PPoly.exists_of_polyTime hV
  obtain ⟨L, hL, hLg⟩ := PPoly.exists_of_oneSidedError (fun n => framedSlice L' n (p.eval n))
    (polynomiallyBounded_complexity_framedSlice hL' (by fun_prop)) (encodes enc)
    (encodesMember enc A) (fun n x ⟨a, ha⟩ hx => by
      have h := (hdec a).1 ((encodesMember_eq_true_iff ha).1 hx)
      rw [ha, List.length_ofFn] at h
      exact h.trans_eq (congrArg (2 * ·) (congrArg Finset.card
        (Finset.filter_congr fun r _ => verifier_eq_true_iff hVL ha _ r rfl))))
    fun n x ⟨a, ha⟩ hx r => by
      have h := (hdec a).2 fun haA => by
        rw [(encodesMember_eq_true_iff ha).2 haA] at hx
        exact Bool.noConfusion hx
      rw [ha, List.length_ofFn] at h
      rw [← Bool.not_eq_true, ← verifier_eq_true_iff hVL ha _ r rfl, Bool.not_eq_true]
      exact h r
  exact ⟨L, hL, mem_iff_of_slice_eq_encodesMember hLg⟩

end Encoded

/-- **BPP ⊆ P/poly** for languages over `Bool`, with words encoded as themselves. -/
theorem PPoly.of_mem_BPP {A : Language Bool}
    (hA : (A : Set (List Bool)) ∈ Complexity.BPP encBits) : A ∈ PPoly := by
  obtain ⟨L, hL, h⟩ := PPoly.exists_of_mem_BPP hA
  exact (Language.ext fun w => h w : A = L) ▸ hL

/-- **RP ⊆ P/poly** for languages over `Bool`, with words encoded as themselves. -/
theorem PPoly.of_mem_RP {A : Language Bool}
    (hA : (A : Set (List Bool)) ∈ Complexity.RP encBits) : A ∈ PPoly := by
  obtain ⟨L, hL, h⟩ := PPoly.exists_of_mem_RP hA
  exact (Language.ext fun w => h w : A = L) ▸ hL

/-- **coRP ⊆ P/poly** for languages over `Bool`. -/
theorem PPoly.of_mem_coRP {A : Language Bool}
    (hA : (A : Set (List Bool)) ∈ Complexity.coRP encBits) : A ∈ PPoly := by
  have h := PPoly.compl (PPoly.of_mem_RP (A := Aᶜ) hA)
  rwa [compl_compl] at h

end Cslib.Circuits.Boolean
