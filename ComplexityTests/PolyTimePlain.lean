/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.P
import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Tactic.PolyTime
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! Tidy polynomial time, `P` and `NP` against upstream plain machines, in both directions: upstream
machines with no tidiness or space guarantees give library certificates, and library certificates,
including the verifier for SAT, give upstream machines within polynomial time and space. The plain
predicate `Turing.MultiTapeTM.ComputableInPolyTime` is proved by `fun_prop` and `polytime` from
plain hypotheses and tidy certificates, with the limits of `fun_prop` tested below. -/

namespace ComplexityTests.PolyTimePlain

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### From upstream machines to the library and back -/

/-- The words equal to `[true]`, a problem on an infinite type. -/
private def single : Set (List Bool) := {[true]}

/-- Upstream's almost-constant machine decides `single` in constant time and zero space. -/
private theorem exists_decidableInTimeAndSpace_single :
    ∃ c, DecidableInTimeAndSpace single encBits (fun _ => c) (fun _ => 0) :=
  computableInTimeAndSpace_of_exists_finite_ne ⟨false, by
    convert Set.finite_singleton [true] using 1
    ext w
    by_cases hw : w ∈ single <;> simp_all [indicator, single]⟩

/-- Words whose first bit is set. -/
private def firstBit : Set (List Bool) := {w | w.headD false = true}

private theorem firstBit_mem_P : firstBit ∈ P encBits :=
  ⟨fun w => w.headD false, by polytime, fun _ => Iff.rfl⟩

/-- Upstream's copy and almost-constant machines certify library `ComputableTidilyInPolyTime` and
`P` membership; conversely, library `P`, `polytime`, and `NP` (`SAT`) certificates yield upstream
machines within polynomial time and space, and time bounds space linearly. -/
example :
    ComputableTidilyInPolyTime (id : List Bool → List Bool) encBits encBits ∧
    single ∈ P encBits ∧
    (∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      DecidableInTimeAndSpace firstBit encBits (fun w => t w.length) (fun w => s w.length)) ∧
    (∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      ComputableInTimeAndSpaceOfLength
        (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
        encBits encBits t s) ∧
    (∃ (p : Polynomial ℕ) (V : Logic.PL.CNF ℕ × List Bool → Bool) (t s : ℕ → ℕ),
      PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
        ComputableInTimeAndSpaceOfLength V (encPair encCNF encBits) encBool t s ∧
          IsVerifier encCNF p V SAT) ∧
    (∃ c, ComputableInTimeAndSpace (id : List Bool → List Bool) encBits encBits
      (fun w => w.length + 1) (fun w => c * (w.length + 1) + c)) := by
  refine ⟨ComputableInTimeAndSpace.computableTidilyInPolyTime (t := fun n => n + 1) (by fun_prop)
      computableInTimeAndSpace_id,
    ?_,
    mem_P_iff_exists_decidableInTimeAndSpace.mp firstBit_mem_P,
    ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength (by polytime),
    mem_NP_iff_exists_computableInTimeAndSpaceOfLength.mp SAT.mem_NP,
    computableInTimeAndSpace_id.exists_space_linear⟩
  obtain ⟨c, h⟩ := exists_decidableInTimeAndSpace_single
  exact mem_P_of_decidableInTimeAndSpace (t := fun _ => c) (s := fun w => 2 ^ w.length)
    (by fun_prop) (h.mono (fun _ => le_rfl) (fun _ => Nat.zero_le _))

/-! ### Plain polynomial time -/

section Plain

variable {α : Type} {enc : α ↪ List Bool}

/-- Plain polynomial-time conversions, `fun_prop` and `polytime` closure under conditionals, pairs,
projections, list lengths, negations, and `PolyTimeReducible` / `P` membership. -/
example {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f g : α → Bool} (hf : ComputableInPolyTime f enc encBool)
    (hg : ComputableInPolyTime g enc encBool)
    {gtidy : α → ℕ} (hgtidy : ComputableTidilyInPolyTime gtidy enc encNat)
    {fp : α → β × γ} (hfp : ComputableInPolyTime fp enc (encPair encB encC))
    {fpt : α → β × γ} (hfpt : ComputableTidilyInPolyTime fpt enc (encPair encB encC))
    {fl : α → List ℕ} (hfl : ComputableInPolyTime fl enc (encList encNat))
    {flt : α → List ℕ} (hflt : ComputableTidilyInPolyTime flt enc (encList encNat))
    {fnb : α → ℕ × Bool} (hfnb : ComputableInPolyTime fnb enc (encPair encNat encBool))
    {fnbt : α → ℕ × Bool} (hfnbt : ComputableTidilyInPolyTime fnbt enc (encPair encNat encBool))
    {list : α → List Bool} (hlist : ComputableInPolyTime list enc encBits)
    {A : Set α} {B : Set β} {Bbool : Set Bool} (hBbool : Bbool ∈ P encBool) :
    ComputableInPolyTime (fun n : ℕ => List.replicate n true) encUnary encBits ∧
    ComputableInPolyTime (fun w : List Bool => w.headD false) encBits encBool ∧
    ComputableTidilyInPolyTime (fun a => !f a) enc encBool ∧
    ComputableInPolyTime (id : List Bool → List Bool) encBits encBits ∧
    (∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      ComputableInTimeAndSpaceOfLength (fun w : List Bool => w.headD false) encBits encBool t s) ∧
    ComputableInPolyTime (fun a => if f a then !g a else g a) enc encBool ∧
    ComputableInPolyTime (fun a => ((gtidy a + 1, f a).2 && f a, gtidy a)) enc
      (encPair encBool encNat) ∧
    (ComputableInPolyTime (fun a => (fp a).1) enc encB ∧
      ComputableInPolyTime (fun a => (fp a).2) enc encC) ∧
    ComputableInPolyTime (fun a => (fl a).length) enc encUnary ∧
    ComputableInPolyTime (fun a => !(fnb a).2) enc encBool ∧
    (ComputableInPolyTime (fun a => (fpt a).1) enc encB ∧
      ComputableInPolyTime (fun a => (fpt a).2) enc encC) ∧
    ComputableInPolyTime (fun a => (flt a).length) enc encUnary ∧
    ComputableInPolyTime (fun a => !(fnbt a).2) enc encBool ∧
    ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encNat ∧
    ComputableInPolyTime (fun a => (list a).foldl (fun reversed bit => bit :: reversed) [])
      enc encBits ∧
    firstBit ∈ P encBits ∧
    ((∃ h : α → β, ComputableInPolyTime h enc encB ∧ ∀ a, a ∈ A ↔ h a ∈ B) ↔
      PolyTimeReducible enc encB A B) ∧
    {a | f a ∈ Bbool} ∈ P enc ∧
    PolyTimeReducible encBits encBits {w : List Bool | w.headD false = true}
      {w | w.headD false = true} := by
  refine ⟨.of_eq fun _ => rfl, ?_, ?_,
    ComputableInTimeAndSpace.computableInPolyTime (t := fun n => n + 1) (s := fun w => 2 ^ w.length)
      (by fun_prop) (computableInTimeAndSpace_id.mono (fun _ => le_rfl) (fun _ => Nat.zero_le _)),
    (by polytime : ComputableInPolyTime (fun w : List Bool => w.headD false) encBits encBool),
    by fun_prop, by fun_prop, ⟨by fun_prop, by fun_prop⟩, by fun_prop, by fun_prop,
    ⟨by fun_prop, by fun_prop⟩, by fun_prop, by fun_prop, by fun_prop, by polytime,
    mem_P.mpr ⟨fun w => w.headD false, by polytime, fun _ => Iff.rfl⟩,
    Iff.rfl, PolyTimeReducible.mem_P ⟨f, by fun_prop, fun _ => Iff.rfl⟩ hBbool,
    ⟨id, .id', fun _ => Iff.rfl⟩⟩
  · rw [computableInPolyTime_iff_computableTidilyInPolyTime]; polytime
  · rw [← computableInPolyTime_iff_computableTidilyInPolyTime]; fun_prop

/-- The ordinary plain scan rule certifies the complete captured callback. Both the list and
callback certificate remain necessary, including when they are supplied as known raw facts. -/
example {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list enc encBits)
    (htest : ComputableTidilyInPolyTime (fun p : α × Bool => test p.1 p.2) (encPair enc encBool)
      encBool)
    {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) :
    ComputableInPolyTime (fun a => (list a).any (test a)) enc encBool ∧
    ComputableInPolyTime (fun a => !f a) enc encBool := by
  refine ⟨?_, ?_⟩
  · fail_if_success (clear hlist; fun_prop)
    fail_if_success (clear htest; fun_prop)
    fun_prop
  · fail_if_success (clear hf; fun_prop)
    fun_prop

end Plain

-- A callback family need not choose an encoding convention; the outer certificate may fix it.
example {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
    {output : γ ↪ List Bool} (f : β → γ) (g : α → β)
    (hf : ComputableInPolyTime f middle output)
    (hg : ∀ encoding : β ↪ List Bool, ComputableInPolyTime g input encoding) :
    ComputableInPolyTime (fun a => f (g a)) input output := by
  fail_if_success (clear hf; fun_prop)
  fun_prop

end ComplexityTests.PolyTimePlain
