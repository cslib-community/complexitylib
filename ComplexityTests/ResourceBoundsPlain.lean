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

/-- The actual copy machine needs no output charge on its zero-workspace realization. -/
theorem id_degree : ComputableInDegree (id : List Bool → List Bool) encBits encBits 1 1 :=
  .of_bounds (DegreeBounded.self.add_const 1) (DegreeBounded.const 0)
    computableInTimeAndSpace_id

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

/-- Constant and copy machines give independent plain polynomial degrees; cost degree two does not
authorize zero output degree; and the cumulative-bound client is inhabited by the copy machine. -/
example {α : Type u} {β : Type v} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (b : β) :
    ComputableInPolyTime (Function.const α b) encIn encOut ∧
    ComputableInDegree (id : List Bool → List Bool) encBits encBits 2 1 ∧
    ¬ComputableInDegree (id : List Bool → List Bool) encBits encBits 2 0 ∧
    ComputableInDegree (id : List Bool → List Bool) encBits encBits 3 2 := by
  refine ⟨(constant_degree encIn encOut b).computableInPolyTime, id_degree.mono, ?_, ?_⟩
  · rintro ⟨_, c, hl⟩
    have h := hl (List.replicate (c + 1) true)
    simp [encBits] at h
  · have h : ComputableInDegree (id : List Bool → List Bool) encBits encBits 3 2 := by
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

/-- The copy machine computes the identity within linear space, in some time. -/
theorem id_computableInSpace :
    ComputableInSpace (id : List Bool → List Bool) encBits encBits (·.length) :=
  ⟨_, 1, computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
    fun w => by simp [encBits]⟩

/-- The copy machine computes the identity within polynomial space. -/
theorem id_computableInPolySpace :
    ComputableInPolySpace (id : List Bool → List Bool) encBits encBits :=
  ⟨_, fun n => n, by fun_prop,
    computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
    fun w => by simp [encBits]⟩

/-- Tidy normal forms keep the bounds up to constants, while the value condition separates
`ComputableInSpace` from `ComputableInLogSpace`. -/
example {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (hlog : ComputableInSpace f encIn encOut fun a => Nat.log2 (encIn a).length) :
    ComputableTidilyInO (id : List Bool → List Bool) encBits encBits (·.length) (·.length) ∧
    ComputableTidilyInSpace (id : List Bool → List Bool) encBits encBits (·.length) ∧
    (¬ComputableInSpace (id : List Bool → List Bool) encBits encBits fun _ => 0) ∧
    ComputableInLogSpace (id : List Bool → List Bool) encBits encBits ∧
    (¬ComputableInSpace (id : List Bool → List Bool) encBits encBits
      fun w => Nat.log2 w.length) ∧
    ComputableInLogSpace f encIn encOut ∧
    ComputableTidilyInPolySpace (id : List Bool → List Bool) encBits encBits := by
  refine ⟨id_computableInO.tidy, id_computableInSpace.tidy, ?_,
    ⟨_, 0, computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩,
    ?_, (let ⟨t, c, hc, _⟩ := hlog; ⟨t, c, hc⟩), id_computableInPolySpace.tidy⟩
  · rintro ⟨t, c, -, hl⟩
    simpa [encBits] using hl (List.replicate (c + 1) true)
  · rintro ⟨t, c, -, hl⟩
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

/-! ### Compositional automation within plain polynomial space -/

/-- The copy machine computes the identity in fpt time, for every parameter. -/
theorem id_computableInFPTTime (κ : List Bool → ℕ) :
    ComputableInFPTTime (id : List Bool → List Bool) encBits encBits κ :=
  ⟨fun _ => 1, 1, computableInTimeAndSpace_id.mono (fun w => by simp [encBits])
    fun _ => Nat.zero_le _⟩

/-- Compose, pair, and branch functions mixing plain space, tidy space, and plain time
certificates; missing certificates fail cleanly; and a time bound alone suffices for fpt time. -/
example {α β γ : Type} (enc : α ↪ List Bool) {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {f : α → β} {g : β → γ} {g' h : α → γ} {c : α → Bool}
    (_u : List Bool → Bool)
    (hf : ComputableInPolySpace f encA encB) (hg : ComputableInPolySpace g encB encC)
    (hg' : ComputableTidilyInPolySpace g' encA encC)
    (hh : ComputableInPolyTime h encA encC) (hc : ComputableInPolyTime c encA encBool)
    (κ : List Bool → ℕ) :
    ComputableInPolySpace (id : α → α) enc enc ∧
    ComputableInPolySpace (fun a => g (f a)) encA encC ∧
    ComputableInPolySpace (fun a => if c a then (f a, g' a) else (f a, h a))
      encA (encPair encB encC) ∧
    ComputableInFPTTime (id : List Bool → List Bool) encBits encBits κ := by
  fail_if_success have : ComputableInPolySpace _u encBits encBool := by fun_prop
  exact ⟨by fun_prop, by fun_prop, by fun_prop,
    ComputableInTimeAndSpace.computableInFPTTime (F := fun _ => 1) (c := 1)
      (s := fun w => 2 ^ w.length)
      (computableInTimeAndSpace_id.mono (fun w => by simp [encBits]) fun _ => Nat.zero_le _)⟩

/-! ### Classes through plain deciders -/

/-- The words equal to `[true]`, a problem on an infinite type. -/
private def single : Set (List Bool) := {[true]}

/-- Upstream's almost-constant machine decides `single` within constant time and zero space. -/
private theorem exists_computableInTimeAndSpace_single : ∃ c,
    ComputableInTimeAndSpace (fun w : List Bool => decide (w = [true])) encBits encBool
      (fun _ => c) fun _ => 0 :=
  computableInTimeAndSpace_of_exists_finite_ne
    ⟨false, (Set.finite_singleton [true]).subset fun w hw => by simpa using hw⟩

/-- Plain polynomial-space and fpt-time deciders give membership in `PSPACE` and `FPT`. -/
example (κ : List Bool → ℕ) : single ∈ PSPACE encBits ∧ single ∈ FPT encBits κ := by
  obtain ⟨c, h⟩ := exists_computableInTimeAndSpace_single
  have hf : ComputableInPolySpace (fun w : List Bool => decide (w = [true])) encBits encBool :=
    ⟨_, fun _ => 1, by fun_prop, h.mono (fun _ => le_rfl) fun _ => Nat.zero_le _,
      fun _ => by simp⟩
  have hfpt : ComputableInFPTTime (fun w : List Bool => decide (w = [true])) encBits encBool κ :=
    ⟨fun _ => c, 0, h.mono (fun _ => by simp) fun _ => Nat.zero_le _⟩
  exact ⟨mem_PSPACE_iff_computableInPolySpace.mpr ⟨_, hf, fun w => by simp [single]⟩,
    mem_FPT_iff_computableInFPTTime.mpr ⟨_, hfpt, fun w => by simp [single]⟩⟩

/-! ### From library certificates to plain ones -/

/-- Tidy library certificates (`Prod.fst`, `polytime` list folds, `TQBF`, and `SAT`) give plain
certificates and compose with plain preprocessing. -/
example {α : Type} {enc : α ↪ List Bool} {f : α → Logic.PL.QBF ℕ}
    (hf : ComputableInPolyTime f enc encQBF) :
    ComputableInO Prod.fst (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length) ∧
    ComputableInSpace Prod.fst (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length) ∧
    ComputableInPolySpace
      (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
      encBits encBits ∧
    (∃ dec, ComputableInPolySpace dec encQBF encBool ∧ ∀ φ, φ ∈ TQBF ↔ dec φ = true) ∧
    {a | f a ∈ TQBF} ∈ PSPACE enc ∧
    (∃ g, ComputableInFPTTime g encCNF encBool Logic.PL.CNF.numVars ∧
      ∀ φ, φ ∈ SAT ↔ g φ = true) := by
  obtain ⟨dec, hdec, hA⟩ := mem_PSPACE_iff_computableInPolySpace.mp TQBF_mem_PSPACE
  have hcomp : ComputableInPolySpace (fun a => dec (f a)) enc encBool := by fun_prop
  obtain ⟨g, hg, hSAT⟩ := mem_FPT_iff_computableInFPTTime.mp SAT_mem_FPT
  exact ⟨.of_tidy (ComputableTidilyInO.fst encBits encBits),
    (ComputableTidilyInSpace.fst encBits encBits).computableInSpace,
    computableInPolySpace_iff_computableTidilyInPolySpace.mpr (.of_polyTime (by polytime)),
    ⟨dec, .of_tidy hdec.tidy, hA⟩,
    mem_PSPACE_iff_computableInPolySpace.mpr ⟨_, hcomp, fun a => hA (f a)⟩,
    ⟨g, hg, hSAT⟩⟩

end ComplexityTests.ResourceBoundsPlain
