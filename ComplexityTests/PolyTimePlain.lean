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

/-! ### From upstream machines to the library -/

/-- Upstream's copy machine, which is not tidy, certifies tidy polynomial time for the identity. -/
example : ComputableTidilyInPolyTime (id : List Bool → List Bool) encBits encBits :=
  ComputableInTimeAndSpace.computableTidilyInPolyTime (t := fun n => n + 1) (by fun_prop)
    computableInTimeAndSpace_id

/-- The words equal to `[true]`, a problem on an infinite type. -/
private def single : Set (List Bool) := {[true]}

/-- Upstream's almost-constant machine decides `single` in constant time and zero space. -/
private theorem exists_decidableInTimeAndSpace_single :
    ∃ c, DecidableInTimeAndSpace single encBits (fun _ => c) (fun _ => 0) :=
  computableInTimeAndSpace_of_exists_finite_ne ⟨false, by
    convert Set.finite_singleton [true] using 1
    ext w
    by_cases hw : w ∈ single <;> simp_all [indicator, single]⟩

/-- A polynomial time bound alone suffices: the space bound may be exponential. -/
example : single ∈ P encBits := by
  obtain ⟨c, h⟩ := exists_decidableInTimeAndSpace_single
  exact mem_P_of_decidableInTimeAndSpace (t := fun _ => c) (s := fun w => 2 ^ w.length)
    (by fun_prop) (h.mono (fun _ => le_rfl) (fun _ => Nat.zero_le _))

/-- The polynomially bounded form of `P` accepts the same upstream decider. -/
example : single ∈ P encBits := by
  obtain ⟨c, h⟩ := exists_decidableInTimeAndSpace_single
  exact mem_P_iff_exists_decidableInTimeAndSpace.mpr
    ⟨fun _ => c, fun _ => 0, by fun_prop, by fun_prop, h⟩

/-! ### From the library to upstream machines -/

/-- Words whose first bit is set. -/
private def firstBit : Set (List Bool) := {w | w.headD false = true}

private theorem firstBit_mem_P : firstBit ∈ P encBits :=
  ⟨fun w => w.headD false, by polytime, fun _ => Iff.rfl⟩

/-- A `polytime` certificate gives an upstream decider within polynomial time and space. -/
example : ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    DecidableInTimeAndSpace firstBit encBits (fun w => t w.length) (fun w => s w.length) :=
  mem_P_iff_exists_decidableInTimeAndSpace.mp firstBit_mem_P

/-- A list program certified by `polytime` is computed by an upstream machine within polynomially
bounded time and space. -/
example : ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    ComputableInTimeAndSpaceOfLength
      (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
      encBits encBits t s :=
  ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength (by polytime)

/-- The SAT verifier is computed by an upstream machine within polynomially bounded time and
space in the length of the encoded formula and assignment. -/
example : ∃ (p : Polynomial ℕ) (V : Logic.PL.CNF ℕ × List Bool → Bool) (t s : ℕ → ℕ),
    PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      ComputableInTimeAndSpaceOfLength V (encPair encCNF encBits) encBool t s ∧
        IsVerifier encCNF p V SAT :=
  mem_NP_iff_exists_computableInTimeAndSpaceOfLength.mp SAT.mem_NP

/-! ### Time bounds space -/

/-- Upstream's copy machine needs no separate space bound beyond a linear function of its time. -/
example : ∃ c, ComputableInTimeAndSpace (id : List Bool → List Bool) encBits encBits
    (fun w => w.length + 1) (fun w => c * (w.length + 1) + c) :=
  computableInTimeAndSpace_id.exists_space_linear

/-! ### Plain polynomial time -/

section Plain

variable {α : Type} {enc : α ↪ List Bool}

/-- The upstream copy machine gives plain polynomial time for any function that leaves the encoded
word unchanged, here the unary encoding of a natural number viewed as bits. -/
example : ComputableInPolyTime (fun n : ℕ => List.replicate n true) encUnary encBits :=
  .of_eq fun _ => rfl

/-- The bridge with the tidy predicate is a single rewrite, in either direction. -/
example : ComputableInPolyTime (fun w : List Bool => w.headD false) encBits encBool := by
  rw [computableInPolyTime_iff_computableTidilyInPolyTime]
  polytime

example {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) :
    ComputableTidilyInPolyTime (fun a => !f a) enc encBool := by
  rw [← computableInPolyTime_iff_computableTidilyInPolyTime]
  fun_prop

/-- A polynomial time bound alone suffices: upstream's copy machine with an exponential space
bound. -/
example : ComputableInPolyTime (id : List Bool → List Bool) encBits encBits :=
  ComputableInTimeAndSpace.computableInPolyTime (t := fun n => n + 1) (s := fun w => 2 ^ w.length)
    (by fun_prop) (computableInTimeAndSpace_id.mono (fun _ => le_rfl) (fun _ => Nat.zero_le _))

/-- A plain certificate unfolds to an upstream machine within polynomially bounded time and space
with no conversion. -/
example : ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    ComputableInTimeAndSpaceOfLength (fun w : List Bool => w.headD false) encBits encBool t s :=
  (by polytime : ComputableInPolyTime (fun w : List Bool => w.headD false) encBits encBool)

/-- Before: without plain closure rules, plain hypotheses are restated tidily, composed, and the
result converted back. -/
example {f g : α → Bool} (hf : ComputableInPolyTime f enc encBool)
    (hg : ComputableInPolyTime g enc encBool) :
    ComputableInPolyTime (fun a => if f a then !g a else g a) enc encBool := by
  have hf := hf.tidy
  have hg := hg.tidy
  exact .of_tidy (by fun_prop)

/-- After: `fun_prop` composes plain hypotheses directly, using tidy certificates such as
`Turing.MultiTapeTM.ComputableTidilyInPolyTime.bool_not` for the known functions. -/
example {f g : α → Bool} (hf : ComputableInPolyTime f enc encBool)
    (hg : ComputableInPolyTime g enc encBool) :
    ComputableInPolyTime (fun a => if f a then !g a else g a) enc encBool := by fun_prop

/-- Pairs and projections of plain hypotheses, with a tidy hypothesis in the same goal. -/
example {f : α → Bool} {g : α → ℕ} (hf : ComputableInPolyTime f enc encBool)
    (hg : ComputableTidilyInPolyTime g enc encNat) :
    ComputableInPolyTime (fun a => ((g a + 1, f a).2 && f a, g a)) enc
      (encPair encBool encNat) := by fun_prop

/-- Projections and calls on the values of pair- and list-valued plain hypotheses: the intermediate
encoding is inferred from the hypothesis. -/
example {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableInPolyTime f enc (encPair encB encC)) :
    ComputableInPolyTime (fun a => (f a).1) enc encB ∧
      ComputableInPolyTime (fun a => (f a).2) enc encC :=
  ⟨by fun_prop, by fun_prop⟩

example {f : α → List ℕ} (hf : ComputableInPolyTime f enc (encList encNat)) :
    ComputableInPolyTime (fun a => (f a).length) enc encUnary := by fun_prop

example {f : α → ℕ × Bool} (hf : ComputableInPolyTime f enc (encPair encNat encBool)) :
    ComputableInPolyTime (fun a => !(f a).2) enc encBool := by fun_prop

/-- The same goals from tidy hypotheses. -/
example {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → β × γ}
    (hf : ComputableTidilyInPolyTime f enc (encPair encB encC)) :
    ComputableInPolyTime (fun a => (f a).1) enc encB ∧
      ComputableInPolyTime (fun a => (f a).2) enc encC :=
  ⟨by fun_prop, by fun_prop⟩

example {f : α → List ℕ} (hf : ComputableTidilyInPolyTime f enc (encList encNat)) :
    ComputableInPolyTime (fun a => (f a).length) enc encUnary := by fun_prop

example {f : α → ℕ × Bool} (hf : ComputableTidilyInPolyTime f enc (encPair encNat encBool)) :
    ComputableInPolyTime (fun a => !(f a).2) enc encBool := by fun_prop

/-- The ordinary plain scan rule certifies the complete captured callback. Both the list and
callback certificate remain necessary, including when they are supplied as known raw facts. -/
example {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list enc encBits)
    (htest : ComputableTidilyInPolyTime (fun p : α × Bool => test p.1 p.2) (encPair enc encBool)
      encBool) :
    ComputableInPolyTime (fun a => (list a).any (test a)) enc encBool := by
  fail_if_success (clear hlist; fun_prop)
  fail_if_success (clear htest; fun_prop)
  fun_prop

example {list : α → List Bool} {test : α → Bool → Bool}
    (hlist : ComputableTidilyInPolyTime list enc encBits)
    (htest : ComputableTidilyInPolyTime (fun p : α × Bool => test p.1 p.2) (encPair enc encBool)
      encBool) :
    ComputableInPolyTime (fun a => (list a).any (test a)) enc encBool := by polytime

/-- Another encoding of the same function uses its own certificate. -/
example : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encNat := by fun_prop

/-- `polytime` accepts plain goals and plain hypotheses, including inside loop rules. -/
example {list : α → List Bool} (hlist : ComputableInPolyTime list enc encBits) :
    ComputableInPolyTime (fun a => (list a).foldl (fun reversed bit => bit :: reversed) [])
      enc encBits := by polytime

/-- Membership in `P` from a plain certificate. -/
example : firstBit ∈ P encBits :=
  ⟨fun w => w.headD false, (by polytime : ComputableInPolyTime _ encBits encBool),
    fun _ => Iff.rfl⟩

/-- Membership in `P` from a certificate built by `polytime`, through `mem_P`. -/
example : firstBit ∈ P encBits :=
  mem_P.mpr ⟨fun w => w.headD false, by polytime, fun _ => Iff.rfl⟩

/-- A reduction stated plainly is the library's polynomial-time reduction, by definition. -/
example {β : Type} {encB : β ↪ List Bool} {A : Set α} {B : Set β} :
    (∃ f : α → β, ComputableInPolyTime f enc encB ∧ ∀ a, a ∈ A ↔ f a ∈ B) ↔
      PolyTimeReducible enc encB A B :=
  Iff.rfl

/-- A reduction built from plain hypotheses with `fun_prop`, and transported along it. -/
example {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) {B : Set Bool}
    (hB : B ∈ P encBool) : {a | f a ∈ B} ∈ P enc :=
  PolyTimeReducible.mem_P ⟨f, by fun_prop, fun _ => Iff.rfl⟩ hB

/-- A reduction by the identity, with the plain identity certificate. -/
example : PolyTimeReducible encBits encBits {w : List Bool | w.headD false = true}
    {w | w.headD false = true} :=
  ⟨id, .id', fun _ => Iff.rfl⟩

/-- Without a hypothesis or a certificate for `f`, `fun_prop` does not claim polynomial time. -/
example {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) :
    ComputableInPolyTime (fun a => !f a) enc encBool := by
  fail_if_success (clear hf; fun_prop)
  fun_prop

end Plain

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInTimeAndSpace.computableTidilyInPolyTime

/--
info: 'Turing.MultiTapeTM.decidableInTimeAndSpace_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms decidableInTimeAndSpace_iff

/--
info: 'Cslib.Complexity.mem_P_iff_exists_decidableInTimeAndSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_P_iff_exists_decidableInTimeAndSpace

/--
info: 'Cslib.Complexity.mem_P_of_decidableInTimeAndSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_P_of_decidableInTimeAndSpace

/--
info: 'Cslib.Complexity.mem_NP_iff_exists_computableInTimeAndSpaceOfLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_NP_iff_exists_computableInTimeAndSpaceOfLength

/--
info: 'Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInPolyTime_iff_computableTidilyInPolyTime

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInPolyTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInTimeAndSpace.computableInPolyTime

end ComplexityTests.PolyTimePlain
