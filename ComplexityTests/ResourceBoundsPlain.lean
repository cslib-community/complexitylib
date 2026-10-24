/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Space.Closure
import Complexity.Computability.Complexity.Classes.Space.TQBF.Membership
import Complexity.Computability.Complexity.Parameterized
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree
import Complexity.Tactic.PolyTime
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! Plain computability within bounds up to constants, within a space bound, within polynomial
space and in fpt time, against the tidy notions in both directions: upstream machines that are not
tidy satisfy the plain notions and give tidy certificates, and library certificates, including
the deciders for `TQBF` and `SAT`, give plain ones. -/

namespace ComplexityTests.ResourceBoundsPlain

universe u v

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Independent plain polynomial degrees -/

/-- A constant machine works on arbitrary encodings in unrelated universes, with zero degrees. -/
theorem constant_degree {α β : Type*} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (b : β) : ComputableInDegree (Function.const α b) encIn encOut 0 0 := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encOut) b
  exact ⟨⟨_, _, DegreeBounded.const c, DegreeBounded.const 0, hc⟩,
    DegreeBounded.const (encOut b).length⟩

example {α : Type u} {β : Type v} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (b : β) :
    ComputableInPolyTime (Function.const α b) encIn encOut :=
  (constant_degree encIn encOut b).computableInPolyTime

/-- The actual copy machine needs no output charge on its zero-workspace realization. -/
theorem id_degree : ComputableInDegree (id : List Bool → List Bool) encBits encBits 1 1 :=
  .of_bounds (DegreeBounded.self.add_const 1) (DegreeBounded.const 0)
    computableInTimeAndSpace_id

example : ComputableInDegree (id : List Bool → List Bool) encBits encBits 2 1 :=
  id_degree.mono

/-- Cost degree two does not authorize replacing the independent output degree by zero. -/
example : ¬ComputableInDegree (id : List Bool → List Bool) encBits encBits 2 0 := by
  rintro ⟨_, c, hl⟩
  have h := hl (List.replicate (c + 1) true)
  simp [encBits] at h

/-- A small cumulative Stretch-shaped bound: quadratic rounds times linear callback cost give
cost degree three, while the seed plus emitted rounds have output degree two. The realization
is supplied once for both independent resource functions. -/
theorem degree_of_streaming_bounds {f : List Bool → List Bool} {c : ℕ}
    (hstream : ComputableInTimeAndSpace f encBits encBits
      (fun w => c * ((w.length + 1) ^ 2 + w.length + w.length ^ 2 +
        w.length ^ 2 * ((w.length + 1) + w.length + 1) + 1))
      (fun w => c * ((w.length + 1) ^ 2 + w.length + w.length ^ 2 + 1)))
    (hl : ∀ w, (f w).length ≤ w.length + w.length ^ 2) :
    ComputableInDegree f encBits encBits 3 2 := by
  have hn : DegreeBounded (fun w : List Bool => w.length) (fun w => w.length) 1 :=
    DegreeBounded.self
  have hp : DegreeBounded (fun w : List Bool => w.length) (fun w => (w.length + 1) ^ 2) 2 :=
    ⟨1, fun _ => by simp⟩
  have hround := ((hn.add_const 1).add hn).add_const 1
  have hn2 : DegreeBounded (fun w : List Bool => w.length) (fun w => w.length ^ 2) 2 := by
    simpa only [pow_two] using hn.mul hn
  have ht := ((((hp.mono_deg (by decide)).add (hn.mono_deg (by decide))).add
    (hn2.mono_deg (by decide))).add (hn2.mul hround)).add_const 1 |>.smul c
  have hs := (((hp.add (hn.mono_deg (by decide))).add hn2).add_const 1).smul c
  exact ⟨⟨_, _, ht, hs.mono_deg (by decide), hstream⟩,
    ((hn.mono_deg (by decide)).add hn2).mono hl⟩

/-- The cumulative-bound client is inhabited by an upstream machine, not merely conditional. -/
example : ComputableInDegree (id : List Bool → List Bool) encBits encBits 3 2 := by
  have h : ComputableInDegree (id : List Bool → List Bool) encBits encBits 3 2 := by
    apply degree_of_streaming_bounds (c := 1)
    · exact computableInTimeAndSpace_id.mono (fun w => by simp [encBits]; omega)
        (fun _ => Nat.zero_le _)
    · intro w
      exact Nat.le_add_right _ _
  fail_if_success
    have : ComputableInDegree (id : List Bool → List Bool) encBits encBits 2 2 := h.mono
  fail_if_success
    have : ComputableInDegree (id : List Bool → List Bool) encBits encBits 3 1 := h.mono
  exact h

/-! ### From upstream machines to tidy certificates -/

/-- Upstream's copy machine, which is not tidy and has no work tape, computes the identity within
linear time and space. -/
theorem id_computableInO :
    ComputableInO (id : List Bool → List Bool) encBits encBits (·.length) (·.length) :=
  ⟨1, computableInTimeAndSpace_id.mono (fun w => by simp [encBits]) fun _ => Nat.zero_le _,
    fun w => by simp [encBits]⟩

/-- The tidy normal form keeps the bounds up to constants. -/
example : ComputableTidilyInO (id : List Bool → List Bool) encBits encBits (·.length) (·.length) :=
  id_computableInO.tidy

/-- The copy machine computes the identity within linear space, in some time. -/
theorem id_computableInSpace :
    ComputableInSpace (id : List Bool → List Bool) encBits encBits (·.length) :=
  ⟨_, 1, computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
    fun w => by simp [encBits]⟩

example : ComputableTidilyInSpace (id : List Bool → List Bool) encBits encBits (·.length) :=
  id_computableInSpace.tidy

/-- The value must fit in the space bound: although the copy machine uses no work space, the
identity is not computable within constant space in this sense. -/
example : ¬ComputableInSpace (id : List Bool → List Bool) encBits encBits fun _ => 0 := by
  rintro ⟨t, c, -, hl⟩
  simpa [encBits] using hl (List.replicate (c + 1) true)

/-- The value condition separates `ComputableInSpace` from the transducer notion
`ComputableInLogSpace`: the copy machine computes the identity in logarithmic space, but the
identity is not computable within space `O(log n)` in the sense of `ComputableInSpace`. -/
example : ComputableInLogSpace (id : List Bool → List Bool) encBits encBits ∧
    ¬ComputableInSpace (id : List Bool → List Bool) encBits encBits
      fun w => Nat.log2 w.length := by
  refine ⟨⟨_, 0, computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩, ?_⟩
  rintro ⟨t, c, -, hl⟩
  have key (n : ℕ) : n * (n + 3) < 2 ^ (n + 2) := by
    induction n with
    | zero => norm_num
    | succ m ih =>
      rcases m with _ | _ | m
      · norm_num
      · norm_num
      · rw [pow_succ]; nlinarith
  have h := hl (List.replicate (2 ^ (c + 2)) true)
  simp only [encBits, id, Function.Embedding.refl_apply, List.length_replicate,
    Nat.log2_two_pow] at h
  nlinarith [key c]

/-- In the other direction, space `O(log n)` in the sense of `ComputableInSpace` is logarithmic
space. -/
example {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (h : ComputableInSpace f encIn encOut fun a => Nat.log2 (encIn a).length) :
    ComputableInLogSpace f encIn encOut :=
  let ⟨t, c, hc, _⟩ := h
  ⟨t, c, hc⟩

/-- The copy machine computes the identity within polynomial space. -/
theorem id_computableInPolySpace :
    ComputableInPolySpace (id : List Bool → List Bool) encBits encBits :=
  ⟨_, fun n => n, by fun_prop,
    computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
    fun w => by simp [encBits]⟩

example : ComputableTidilyInPolySpace (id : List Bool → List Bool) encBits encBits :=
  id_computableInPolySpace.tidy

/-! ### Compositional automation within plain polynomial space -/

example {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolySpace (id : α → α) enc enc := by
  fun_prop

/-- Compose functions with plain certificates without converting either hypothesis by hand. -/
example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β} {g : β → γ}
    (hf : ComputableInPolySpace f encA encB) (hg : ComputableInPolySpace g encB encC) :
    ComputableInPolySpace (fun a => g (f a)) encA encC := by
  fun_prop

/-- Pairing and case distinction can mix plain space, tidy space and plain time certificates. -/
example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β} {g h : α → γ} {c : α → Bool}
    (hf : ComputableInPolySpace f encA encB) (hg : ComputableTidilyInPolySpace g encA encC)
    (hh : ComputableInPolyTime h encA encC) (hc : ComputableInPolyTime c encA encBool) :
    ComputableInPolySpace (fun a => if c a then (f a, g a) else (f a, h a))
      encA (encPair encB encC) := by
  fun_prop

/-- Missing certificates fail instead of cycling between the plain and tidy predicates. -/
example {f : List Bool → Bool} : f = f := by
  fail_if_success have : ComputableInPolySpace f encBits encBool := by fun_prop
  rfl

/-- The copy machine computes the identity in fpt time, for every parameter. -/
theorem id_computableInFPTTime (κ : List Bool → ℕ) :
    ComputableInFPTTime (id : List Bool → List Bool) encBits encBits κ :=
  ⟨fun _ => 1, 1, computableInTimeAndSpace_id.mono (fun w => by simp [encBits])
    fun _ => Nat.zero_le _⟩

/-- A time bound alone suffices for fpt time: the space bound may be exponential. -/
example (κ : List Bool → ℕ) :
    ComputableInFPTTime (id : List Bool → List Bool) encBits encBits κ :=
  ComputableInTimeAndSpace.computableInFPTTime (F := fun _ => 1) (c := 1)
    (s := fun w => 2 ^ w.length)
    (computableInTimeAndSpace_id.mono (fun w => by simp [encBits]) fun _ => Nat.zero_le _)

/-! ### Classes through plain deciders -/

/-- The words equal to `[true]`, a problem on an infinite type. -/
private def single : Set (List Bool) := {[true]}

/-- Upstream's almost-constant machine decides `single` within constant time and zero space. -/
private theorem exists_computableInTimeAndSpace_single : ∃ c,
    ComputableInTimeAndSpace (fun w : List Bool => decide (w = [true])) encBits encBool
      (fun _ => c) fun _ => 0 :=
  computableInTimeAndSpace_of_exists_finite_ne
    ⟨false, (Set.finite_singleton [true]).subset fun w hw => by simpa using hw⟩

/-- A plain polynomial-space decider gives membership in `PSPACE`. -/
example : single ∈ PSPACE encBits := by
  obtain ⟨c, h⟩ := exists_computableInTimeAndSpace_single
  have hf : ComputableInPolySpace (fun w : List Bool => decide (w = [true])) encBits encBool :=
    ⟨_, fun _ => 1, by fun_prop, h.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
      fun _ => by simp⟩
  exact mem_PSPACE_iff_computableInPolySpace.mpr
    ⟨_, hf, fun w => by simp [single]⟩

/-- A plain fpt-time decider gives membership in `FPT`, for every parameter. -/
example (κ : List Bool → ℕ) : single ∈ FPT encBits κ := by
  obtain ⟨c, h⟩ := exists_computableInTimeAndSpace_single
  have hf : ComputableInFPTTime (fun w : List Bool => decide (w = [true])) encBits encBool κ :=
    ⟨fun _ => c, 0, h.mono (fun _ => by simp) fun _ => Nat.zero_le _⟩
  exact mem_FPT_iff_computableInFPTTime.mpr
    ⟨_, hf, fun w => by simp [single]⟩

/-! ### From library certificates to plain ones -/

/-- The first projection, from its tidy certificate. -/
example : ComputableInO Prod.fst (encPair encBits encBits) encBits
    (fun p => (encPair encBits encBits p).length) fun p => (encPair encBits encBits p).length :=
  .of_tidy (ComputableTidilyInO.fst encBits encBits)

/-- The first projection within linear space, from its tidy certificate. -/
example : ComputableInSpace Prod.fst (encPair encBits encBits) encBits
    fun p => (encPair encBits encBits p).length :=
  (ComputableTidilyInSpace.fst encBits encBits).computableInSpace

/-- A list program certified by `polytime` is computable within polynomial space. -/
example : ComputableInPolySpace
    (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
    encBits encBits :=
  computableInPolySpace_iff_computableTidilyInPolySpace.mpr (.of_polyTime (by polytime))

/-- `TQBF` has a plain polynomial-space decider. -/
example : ∃ f, ComputableInPolySpace f encQBF encBool ∧ ∀ φ, φ ∈ TQBF ↔ f φ = true := by
  obtain ⟨f, hf, hA⟩ := mem_PSPACE_iff_computableInPolySpace.mp TQBF_mem_PSPACE
  exact ⟨f, .of_tidy hf.tidy, hA⟩

/-- A plain polynomial-time preprocessing of the existing TQBF decider stays in `PSPACE`.
The decider's tidy certificate and the preprocessing's plain certificate compose automatically. -/
example {α : Type} {enc : α ↪ List Bool} {f : α → Logic.PL.QBF ℕ}
    (hf : ComputableInPolyTime f enc encQBF) : {a | f a ∈ TQBF} ∈ PSPACE enc := by
  obtain ⟨dec, hdec, hA⟩ := mem_PSPACE_iff_computableInPolySpace.mp TQBF_mem_PSPACE
  have hcomp : ComputableInPolySpace (fun a => dec (f a)) enc encBool := by fun_prop
  exact mem_PSPACE_iff_computableInPolySpace.mpr ⟨_, hcomp, fun a => hA (f a)⟩

/-- `SAT` has a plain fpt-time decider in the number of variables. -/
example : ∃ g, ComputableInFPTTime g encCNF encBool Logic.PL.CNF.numVars ∧
    ∀ φ, φ ∈ SAT ↔ g φ = true := by
  obtain ⟨g, hg, hA⟩ := mem_FPT_iff_computableInFPTTime.mp SAT_mem_FPT
  exact ⟨g, hg, hA⟩

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInO' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInTimeAndSpace.computableTidilyInO

/--
info: 'Turing.MultiTapeTM.computableInO_iff_computableTidilyInO' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInO_iff_computableTidilyInO

/--
info: 'Turing.MultiTapeTM.computableInSpace_iff_computableTidilyInSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInSpace_iff_computableTidilyInSpace

/--
info: 'Turing.MultiTapeTM.computableInPolySpace_iff_computableTidilyInPolySpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms computableInPolySpace_iff_computableTidilyInPolySpace

/--
info: 'Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInFPTTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComputableInTimeAndSpace.computableInFPTTime

end ComplexityTests.ResourceBoundsPlain
