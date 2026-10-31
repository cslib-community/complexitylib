/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Bounded existential quantification in exponential time

A test `f` that is computable in polynomial time can be tried on every word of length `ℓ x`,
for `ℓ` computable in polynomial time, within time `2 ^ O(|x| + ℓ x)`
(`Cslib.Complexity.exists_computableInO_any_enumList`). The candidates are enumerated in place:
the existential is reachability within two steps from the all-zero word to the all-one word of
width `ℓ x + 1`, along an edge to `true :: w` for each accepted `w` and from every word starting
with `true` to the all-one word (`Cslib.Complexity.boundedExistsEdge`). Savitch's algorithm
decides it at depth `1` (`Cslib.Reachability.computableInO_savitch`). Every polynomial in the
cost is absorbed by the exponential, so the exponent is linear in `|x| + ℓ x`, with a constant
that depends on the test.

The same edges give the closure of `PSPACE` under bounded existential quantification
(`Cslib.Complexity.setOf_exists_mem_PSPACE`), where the point is the space of the run. Here the
time is the point: this brute force is the last step of lazy diagonalization for
nondeterministic time, which must decide deterministically whether some certificate is
accepted.

## Main definitions

* `Cslib.Complexity.boundedExistsEdge`: the edges of the two-step reachability problem.

## Main results

* `Cslib.Complexity.savitch_boundedExistsEdge`: Savitch's algorithm at depth `1` on these edges
  decides the bounded existential.
* `Cslib.Complexity.exists_computableInO_any_enumList`: the bounded existential within time and
  space `2 ^ O(|x| + ℓ x)`.
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- The edges of the graph on words of width `n + 1` whose reachability within two steps from the
all-zero word to the all-one word is a bounded existential over `f`: an edge from the all-zero word
to `true :: w` when `f (x, w)`, and from every word starting with `true` to the all-one word. -/
@[expose] def boundedExistsEdge {β : Type} (f : β × List Bool → Bool) (x : β) (u v : List Bool) :
    Bool :=
  if !(u.any fun b => b) && v.headD false then f (x, v.tail)
  else u.headD false && !(v.any fun b => !b)

/-- Savitch's algorithm at depth `1` on the edges of `Cslib.Complexity.boundedExistsEdge` decides
the bounded existential. -/
theorem savitch_boundedExistsEdge {β : Type} (f : β × List Bool → Bool) (x : β) (n : ℕ) :
    Cslib.Reachability.savitch (boundedExistsEdge f x) (n + 1) 1 (List.replicate (n + 1) false)
      (List.replicate (n + 1) true) = true ↔ ∃ w : List Bool, w.length = n ∧ f (x, w) = true := by
  rw [Cslib.Reachability.savitch_eq]
  simp only [Cslib.Reachability.reach, List.any_eq_true, Cslib.BitString.mem_enumList,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨m, hm, h₁ | h₁, h₂ | h₂⟩
    · subst h₁
      exact absurd h₂ (by simp [List.replicate_succ])
    · subst h₁
      refine ⟨List.replicate n true, List.length_replicate .., ?_⟩
      simpa [boundedExistsEdge, List.replicate_succ] using h₂
    · subst h₂
      refine ⟨List.replicate n true, List.length_replicate .., ?_⟩
      simpa [boundedExistsEdge, List.replicate_succ] using h₁
    · obtain ⟨b, w, rfl⟩ := List.exists_cons_of_length_eq_add_one hm
      refine ⟨w, by simpa using hm, ?_⟩
      cases b <;> simp_all [boundedExistsEdge, List.replicate_succ]
  · rintro ⟨w, hw, hf⟩
    refine ⟨true :: w, by simp [hw], Or.inr ?_, Or.inr ?_⟩
    · simp [boundedExistsEdge, List.replicate_succ, hf]
    · simp [boundedExistsEdge, List.replicate_succ]

/-- A polynomially bounded resource function is within a constant multiple of `2 ^ size`. -/
private theorem PolyBounded.exists_le_mul_two_pow {α : Type*} {size u : α → ℕ}
    (h : PolyBounded size u) : ∃ C, ∀ a, u a ≤ C * 2 ^ size a := by
  obtain ⟨c, d, hcd⟩ := h.exists_le
  obtain ⟨C, hC⟩ := PolynomiallyBounded.exists_le_mul_two_pow
    (p := fun n => c * (n + 1) ^ d) (by fun_prop)
  exact ⟨C, fun a => (hcd a).trans (hC _)⟩

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd'
    ComputableInPolyTime.bool_and' in
/-- **Bounded existential quantification in exponential time.** If a test `f` is computable within
time and space polynomial in its encoded input, and `ℓ` is computable in unary in polynomial time,
then whether some word of length `ℓ x` passes `f` with `x` is computable within time and space
`2 ^ (K * ((encB x).length + ℓ x))` for a constant `K`. Savitch's algorithm decides it at depth `1`
on the edges of `Cslib.Complexity.boundedExistsEdge`. -/
theorem exists_computableInO_any_enumList {β : Type} {encB : β ↪ List Bool}
    {f : β × List Bool → Bool} {Tf Sf : β × List Bool → ℕ}
    (hf : ComputableInO f (encPair encB encBits) encBool Tf Sf)
    (hTf : PolyBounded (fun q => (encPair encB encBits q).length) Tf)
    (hSf : PolyBounded (fun q => (encPair encB encBits q).length) Sf)
    {ℓ : β → ℕ} (hℓ : ComputableInPolyTime ℓ encB encUnary) :
    ∃ K, ComputableInO (fun x => (Cslib.BitString.enumList (ℓ x)).any fun w => f (x, w)) encB
      encBool (fun x => 2 ^ (K * ((encB x).length + ℓ x)))
      (fun x => 2 ^ (K * ((encB x).length + ℓ x))) := by
  set encQ := encPair encB (encPair encBits encBits)
  -- the edge test: polynomial-time tests around one call of `f`
  have hg : ComputableInPolyTime (fun q : β × List Bool × List Bool => (q.1, q.2.2.tail))
      encQ (encPair encB encBits) := by fun_prop
  have hc : ComputableInPolyTime
      (fun q : β × List Bool × List Bool => !(q.2.1.any fun b => b) && q.2.2.headD false)
      encQ encBool := by fun_prop
  have he : ComputableInPolyTime
      (fun q : β × List Bool × List Bool => q.2.1.headD false && !(q.2.2.any fun b => !b))
      encQ encBool := by fun_prop
  obtain ⟨Tg, Sg, hTg, hSg, hgO⟩ := hg.exists_computableInO
  obtain ⟨Tc, Sc, hTc, hSc, hcO⟩ := hc.exists_computableInO
  obtain ⟨Te, Se, hTe, hSe, heO⟩ := he.exists_computableInO
  have hedge := hcO.ite (hf.comp hgO) heO
  -- the arguments of Savitch's algorithm
  have hin : ComputableInPolyTime
      (fun x => (x, ℓ x + 1, 1, List.replicate (ℓ x + 1) false, List.replicate (ℓ x + 1) true))
      encB (Cslib.Reachability.encArgs encB) := by
    unfold Cslib.Reachability.encArgs
    fun_prop
  obtain ⟨Ti, Si, hTi, hSi, hinO⟩ := hin.exists_computableInO
  have h := Cslib.Reachability.computableInO_savitch (edge := boundedExistsEdge f) (par := id)
    hedge hinO (fun _ => List.length_replicate ..) fun _ => List.length_replicate ..
  -- every polynomial is within a constant multiple of an exponential
  have hpoly (T₁ T₂ T₃ : β × List Bool × List Bool → ℕ) (T : β × List Bool → ℕ)
      (h₁ : PolyBounded (fun q => (encQ q).length) T₁)
      (h₂ : PolyBounded (fun q => (encQ q).length) T₂)
      (h₃ : PolyBounded (fun q => (encQ q).length) T₃)
      (hT : PolyBounded (fun q => (encPair encB encBits q).length) T) :
      ∃ C, ∀ q, (T₁ q + if !(q.2.1.any fun b => b) && q.2.2.headD false then
        T₂ q + T (q.1, q.2.2.tail) else T₃ q) ≤ C * 2 ^ (encQ q).length := by
    have hcomp : PolyBounded (fun q => (encQ q).length) fun q => T (q.1, q.2.2.tail) :=
      hT.comp hg.polyBounded_length
    refine PolyBounded.exists_le_mul_two_pow
      ((h₁.add ((h₂.add hcomp).add h₃)).mono fun q => ?_)
    split_ifs <;> omega
  obtain ⟨CT, hCT⟩ := hpoly Tc Tg Te Tf hTc hTg hTe hTf
  obtain ⟨CS, hCS⟩ := hpoly Sc Sg Se Sf hSc hSg hSe hSf
  obtain ⟨CI, hCI⟩ := PolyBounded.exists_le_mul_two_pow hTi
  obtain ⟨CJ, hCJ⟩ := PolyBounded.exists_le_mul_two_pow hSi
  -- the edge queries on words of width `ℓ x + 1`
  have hq (x : β) {u v : List Bool} (hu : u ∈ Cslib.BitString.enumList (ℓ x + 1))
      (hv : v ∈ Cslib.BitString.enumList (ℓ x + 1)) :
      (encQ (x, u, v)).length = 2 * (encB x).length + 3 * ℓ x + 5 := by
    simp only [encQ, length_encPair, encBits_apply, Cslib.BitString.mem_enumList.mp hu,
      Cslib.BitString.mem_enumList.mp hv]
    ring
  refine ⟨12, (h.mono ((CI + CJ + CT + CS + 1) * 2 ^ 26) (fun x => ?_) fun x => ?_).of_enc_eq
    fun x => ?_⟩
  · -- time
    set n := (encB x).length
    set L := ℓ x
    have hmax := listMax_le (f := fun u => listMax (fun v => (Tc (x, u, v) +
        if !(u.any fun b => b) && v.headD false then Tg (x, u, v) + Tf (x, v.tail)
        else Te (x, u, v))) (Cslib.BitString.enumList (L + 1)))
      (l := Cslib.BitString.enumList (L + 1)) (b := CT * 2 ^ (2 * n + 3 * L + 5))
      fun u hu => listMax_le fun v hv => (hCT (x, u, v)).trans_eq (by rw [hq x hu hv])
    change Ti x + 2 ^ ((L + 1 + 2) * (1 + 1)) * (((1 + 1) * (1 + (L + 1) + 1) + n + 1) ^ 2 +
      Cslib.Reachability.edgeMax _ x (L + 1)) ≤ _
    unfold Cslib.Reachability.edgeMax
    have hTi := hCI x
    have hsq : ((1 + 1) * (1 + (L + 1) + 1) + n + 1) ^ 2 ≤ 2 ^ (2 * (2 * L + n + 7)) :=
      calc _ ≤ (2 * L + n + 7) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ (2 ^ (2 * L + n + 7)) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
        _ = _ := by rw [← pow_mul, mul_comm]
    have hE : 2 ^ ((L + 1 + 2) * (1 + 1)) * (2 ^ (2 * (2 * L + n + 7)) +
        CT * 2 ^ (2 * n + 3 * L + 5)) ≤ (CT + 1) * 2 ^ (12 * (n + L)) * 2 ^ 26 := by
      have h₁ : 2 ^ ((L + 1 + 2) * (1 + 1)) * 2 ^ (2 * (2 * L + n + 7)) ≤
          2 ^ (12 * (n + L)) * 2 ^ 26 := by
        rw [← pow_add, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by ring_nf; omega)
      have h₂ : 2 ^ ((L + 1 + 2) * (1 + 1)) * 2 ^ (2 * n + 3 * L + 5) ≤
          2 ^ (12 * (n + L)) * 2 ^ 26 := by
        rw [← pow_add, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by ring_nf; omega)
      have := Nat.mul_le_mul_left CT h₂
      nlinarith
    have hI : 2 ^ n ≤ 2 ^ (12 * (n + L)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmono := Nat.mul_le_mul_left (2 ^ ((L + 1 + 2) * (1 + 1)))
      (Nat.add_le_add hsq hmax)
    have hX : 1 ≤ 2 ^ (12 * (n + L)) := Nat.one_le_two_pow
    calc _ ≤ CI * 2 ^ n + (CT + 1) * 2 ^ (12 * (n + L)) * 2 ^ 26 :=
          Nat.add_le_add hTi (hmono.trans hE)
      _ ≤ _ := by nlinarith
  · -- space
    set n := (encB x).length
    set L := ℓ x
    have hmax := listMax_le (f := fun u => listMax (fun v => (Sc (x, u, v) +
        if !(u.any fun b => b) && v.headD false then Sg (x, u, v) + Sf (x, v.tail)
        else Se (x, u, v))) (Cslib.BitString.enumList (L + 1)))
      (l := Cslib.BitString.enumList (L + 1)) (b := CS * 2 ^ (2 * n + 3 * L + 5))
      fun u hu => listMax_le fun v hv => (hCS (x, u, v)).trans_eq (by rw [hq x hu hv])
    change Si x + (1 + 1) * (1 + (L + 1) + 1) + n + Cslib.Reachability.edgeMax _ x (L + 1) ≤ _
    unfold Cslib.Reachability.edgeMax
    have hSi := hCJ x
    have hX : 2 ^ (2 * n + 3 * L + 5) ≤ 2 ^ (12 * (n + L)) * 2 ^ 5 := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hI : 2 ^ n ≤ 2 ^ (12 * (n + L)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hL : (1 + 1) * (1 + (L + 1) + 1) + n ≤ 6 * 2 ^ (12 * (n + L)) := by
      have : n + L < 2 ^ (n + L) := Nat.lt_two_pow_self
      have : 2 ^ (n + L) ≤ 2 ^ (12 * (n + L)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have := Nat.mul_le_mul_left CS hX
    nlinarith
  · congr 1
    rw [Bool.eq_iff_iff, id, savitch_boundedExistsEdge f x (ℓ x)]
    simp only [List.any_eq_true, Cslib.BitString.mem_enumList]

end Cslib.Complexity
