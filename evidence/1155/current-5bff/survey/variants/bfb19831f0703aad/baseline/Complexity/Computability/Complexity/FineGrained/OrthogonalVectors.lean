/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Exponents
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# The strong exponential time hypothesis implies the orthogonal vectors hypothesis

The split-and-list reduction of Williams [Williams2005] (`Cslib.Complexity.toOV`) splits the `n`
distinct variables of a formula with `m` clauses into halves of `⌊n / 2⌋` and `⌈n / 2⌉` variables.
To each assignment of a half it assigns the vector of length `m` whose coordinate `j` is `true`
when no literal of clause `j` on a variable of the half is satisfied
(`Cslib.Complexity.OV.clauseVector`). Two such vectors, one for each half, are orthogonal exactly
when every clause is satisfied by one of the two partial assignments, that is when together they
satisfy the formula. So the formula is satisfiable exactly when the instance `toOV φ`, of
`2 ^ ⌊n / 2⌋` and `2 ^ ⌈n / 2⌉` vectors of dimension `m`, is in `OV`
(`Cslib.Complexity.toOV_mem_OV_iff`).

The reduction writes its output of about `2 ^ ⌈n / 2⌉ m` bits within time `2 ^ ⌈n / 2⌉` times a
polynomial in the length of the encoded formula
(`Cslib.Complexity.exists_computableInO_toOV`). The vectors are streamed to the output one
at a time (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum`);
accumulating them in a list would cost time quadratic in the number of vectors. Then a decider
for `OV` within time `N ^ (2 - ε)` times a polynomial in the dimension, on `N` vectors, decides
`SAT` within time `2 ^ ((1 - ε / 2) n)` times a polynomial, for `0 < ε ≤ 1`
(`Cslib.Complexity.DecidableInTimeO.decidableInExpTime_SAT`), and the strong exponential time
hypothesis implies the orthogonal vectors hypothesis (`Cslib.Complexity.OVH_of_SETH`).

The orthogonal vectors hypothesis is stated with a polynomial factor in the dimension. Its form for
dimension `c log N`, which follows from the strong exponential time hypothesis with the
sparsification lemma, is not proved here.

## Main definitions

* `Cslib.Complexity.OV.clauseVector`, `Cslib.Complexity.OV.halfVectors`: the vectors of the
  assignments of a half of the variables.
* `Cslib.Complexity.toOV`: the split-and-list reduction.

## Main results

* `Cslib.Complexity.toOV_mem_OV_iff`: `toOV φ ∈ OV ↔ φ ∈ SAT`.
* `Cslib.Complexity.exists_computableInO_toOV`: the reduction runs within time
  `2 ^ ⌈n / 2⌉` times a polynomial.
* `Cslib.Complexity.DecidableInTimeO.decidableInExpTime_SAT`: a fast `OV` decider gives a fast
  `SAT` decider.
* `Cslib.Complexity.OVH_of_SETH`: `SETH → OVH`.

## References

* [R. Williams, *A new algorithm for optimal 2-constraint satisfaction and its
  implications*][Williams2005]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Orthogonality -/

/-- Vectors indexed by the same list are orthogonal when no index is `true` in both. -/
theorem OV.orthogonal_map_map {γ : Type*} {l : List γ} {f g : γ → Bool} :
    OV.Orthogonal (l.map f) (l.map g) ↔ ∀ x ∈ l, f x = false ∨ g x = false := by
  constructor
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    simpa [List.getD_eq_getElem?_getD, hj] using h j
  · intro h j
    rcases lt_or_ge j l.length with hj | hj
    · simpa [List.getD_eq_getElem?_getD, hj] using h _ (List.getElem_mem hj)
    · left
      simp [List.getD_eq_getElem?_getD, hj]

/-! ### The split-and-list reduction -/

namespace OV

/-- Whether the assignment numbered by `i` on the variables `vs` satisfies a literal of the clause
`c` on a variable of `vs`. -/
def satisfiesOn (vs : List ℕ) (i : ℕ) (c : Clause ℕ) : Bool :=
  c.any fun l => decide (l.1 ∈ vs) && bitsAssignment vs i l.1 == l.2

/-- The vector of the assignment numbered by `i` on the variables `vs`: coordinate `j` is `true`
when the assignment satisfies no literal of clause `j` of `φ` on a variable of `vs`. -/
def clauseVector (φ : CNF ℕ) (vs : List ℕ) (i : ℕ) : List Bool :=
  φ.map fun c => !satisfiesOn vs i c

/-- The vectors of the `2 ^ |vs|` assignments numbered on the variables `vs`. -/
def halfVectors (φ : CNF ℕ) (vs : List ℕ) : List (List Bool) :=
  (List.range (2 ^ vs.length)).map (clauseVector φ vs)

/-- The first `⌊n / 2⌋` of the `n` distinct variables. -/
def firstVars (φ : CNF ℕ) : List ℕ :=
  φ.distinctVars.take (φ.distinctVars.length / 2)

/-- The last `⌈n / 2⌉` of the `n` distinct variables. -/
def secondVars (φ : CNF ℕ) : List ℕ :=
  φ.distinctVars.drop (φ.distinctVars.length / 2)

end OV

/-- **The split-and-list reduction** [Williams2005]: the vectors of the assignments of the first
`⌊n / 2⌋` and of the last `⌈n / 2⌉` of the `n` distinct variables of a formula. -/
def toOV (φ : CNF ℕ) : List (List Bool) × List (List Bool) :=
  (OV.halfVectors φ (OV.firstVars φ), OV.halfVectors φ (OV.secondVars φ))

namespace OV

theorem satisfiesOn_eq_true_iff {vs : List ℕ} {i : ℕ} {c : Clause ℕ} :
    satisfiesOn vs i c = true ↔ ∃ l ∈ c, l.1 ∈ vs ∧ bitsAssignment vs i l.1 = l.2 := by
  simp [satisfiesOn]

theorem length_firstVars (φ : CNF ℕ) : (firstVars φ).length = φ.numVars / 2 := by
  simp only [firstVars, List.length_take, CNF.length_distinctVars]
  omega

theorem length_secondVars (φ : CNF ℕ) :
    (secondVars φ).length = φ.numVars - φ.numVars / 2 := by
  simp [secondVars, CNF.length_distinctVars]

theorem length_halfVectors (φ : CNF ℕ) (vs : List ℕ) :
    (halfVectors φ vs).length = 2 ^ vs.length := by
  simp [halfVectors]

theorem length_of_mem_halfVectors {φ : CNF ℕ} {vs : List ℕ} {v : List Bool}
    (hv : v ∈ halfVectors φ vs) : v.length = φ.length := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  simp [clauseVector]

/-- **Orthogonal vectors are satisfying assignments.** For disjoint lists of variables `vs₁` and
`vs₂` covering the variables of `φ`, the vectors of the assignments numbered by `i₁` on `vs₁` and
by `i₂` on `vs₂` are orthogonal exactly when the two assignments together satisfy `φ`. -/
theorem orthogonal_clauseVector_iff {φ : CNF ℕ} {vs₁ vs₂ : List ℕ} (hdisj : vs₁.Disjoint vs₂)
    (hcover : ∀ v ∈ φ.vars, v ∈ vs₁ ∨ v ∈ vs₂) (i₁ i₂ : ℕ) :
    Orthogonal (clauseVector φ vs₁ i₁) (clauseVector φ vs₂ i₂) ↔
      φ.eval (fun v => if v ∈ vs₁ then bitsAssignment vs₁ i₁ v else bitsAssignment vs₂ i₂ v) =
        true := by
  rw [clauseVector, clauseVector, orthogonal_map_map, CNF.eval_eq_true_iff]
  refine forall₂_congr fun c hc => ?_
  simp only [Bool.not_eq_false', satisfiesOn_eq_true_iff, Clause.eval_eq_true_iff]
  constructor
  · rintro (⟨l, hl, hv, he⟩ | ⟨l, hl, hv, he⟩)
    · exact ⟨l, hl, by rw [ite_eq_left hv, he]⟩
    · exact ⟨l, hl, by rw [ite_eq_right fun h => hdisj h hv, he]⟩
  · rintro ⟨l, hl, he⟩
    have hvars : l.1 ∈ φ.vars := List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩
    by_cases hv : l.1 ∈ vs₁
    · exact Or.inl ⟨l, hl, hv, by rwa [ite_eq_left hv] at he⟩
    · exact Or.inr ⟨l, hl, (hcover _ hvars).resolve_left hv, by rwa [ite_eq_right hv] at he⟩

end OV

/-- **The split-and-list reduction is correct** [Williams2005]: `toOV φ ∈ OV ↔ φ ∈ SAT`. -/
theorem toOV_mem_OV_iff (φ : CNF ℕ) : toOV φ ∈ OV ↔ φ ∈ SAT := by
  set vs := φ.distinctVars
  set h := vs.length / 2
  have hdisj : (vs.take h).Disjoint (vs.drop h) :=
    List.disjoint_of_nodup_append (by rw [List.take_append_drop]; exact φ.nodup_distinctVars)
  have hcover : ∀ v ∈ φ.vars, v ∈ vs.take h ∨ v ∈ vs.drop h := fun v hv => by
    rw [← List.mem_append, List.take_append_drop]
    exact CNF.mem_distinctVars.mpr hv
  simp only [toOV, OV, OV.halfVectors, Set.mem_ofPred_eq, List.mem_map, List.mem_range,
    exists_exists_and_eq_and]
  rw [mem_SAT]
  constructor
  · rintro ⟨i₁, -, i₂, -, ho⟩
    exact ⟨_, (OV.orthogonal_clauseVector_iff hdisj hcover i₁ i₂).mp ho⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨i₁, hi₁, h₁⟩ := exists_lt_two_pow_bitsAssignment_eq (vs := vs.take h) σ
    obtain ⟨i₂, hi₂, h₂⟩ := exists_lt_two_pow_bitsAssignment_eq (vs := vs.drop h) σ
    refine ⟨i₁, hi₁, i₂, hi₂, (OV.orthogonal_clauseVector_iff hdisj hcover i₁ i₂).mpr ?_⟩
    refine (CNF.eval_congr fun v hv => ?_).trans hσ
    split_ifs with hv₁
    · exact h₁ v hv₁
    · exact h₂ v ((hcover v hv).resolve_left hv₁)

/-! ### Sizes -/

theorem length_toOV_fst (φ : CNF ℕ) : (toOV φ).1.length = 2 ^ (φ.numVars / 2) := by
  rw [toOV, OV.length_halfVectors, OV.length_firstVars]

theorem length_toOV_snd (φ : CNF ℕ) : (toOV φ).2.length = 2 ^ (φ.numVars - φ.numVars / 2) := by
  rw [toOV, OV.length_halfVectors, OV.length_secondVars]

/-- The dimension is at most a bound on the lengths of all vectors. -/
theorem OV.dim_le {p : List (List Bool) × List (List Bool)} {b : ℕ}
    (h : ∀ v ∈ p.1 ++ p.2, v.length ≤ b) : OV.dim p ≤ b :=
  listMax_le h

/-- The vectors of `toOV φ` have one coordinate for each clause. -/
theorem OV.dim_toOV_le (φ : CNF ℕ) : OV.dim (toOV φ) ≤ φ.length :=
  OV.dim_le fun v hv => by
    rcases List.mem_append.mp hv with hv | hv <;>
      exact (OV.length_of_mem_halfVectors hv).le

/-! ### Running time -/

/-- `2 ^ h` in unary, by doubling `1` repeatedly. -/
private theorem unary_two_pow {γ : Type} {encIn : γ ↪ List Bool} {h : γ → ℕ} {Th Sh : γ → ℕ}
    (hh : ComputableTidilyInO h encIn encNat Th Sh) :
    ComputableTidilyInO (fun x => 2 ^ h x) encIn encUnary
      (fun x => Th x + (encIn x).length +
        (h x + 1) * (2 * 2 ^ h x + 2 ^ h x + ((encNat (h x)).length + 1) ^ 2))
      fun x => Sh x + (encIn x).length + 2 * 2 ^ h x + 2 ^ h x + (encNat (h x)).length := by
  have hid : ComputableTidilyInO (fun m : ℕ => m) encUnary encUnary (fun m => (encUnary m).length)
      fun m => (encUnary m).length := ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)
  have hdouble : ComputableTidilyInO (fun m : ℕ => 2 * m) encUnary encUnary
      (fun m => (encUnary m).length + (encUnary m).length)
      fun m => (encUnary m).length + (encUnary m).length :=
    ComputableTidilyInO.append hid hid fun m => by
      simp only [encUnary_apply, two_mul, List.replicate_add]
  have hiter (k : ℕ) : (fun m : ℕ => 2 * m)^[k] 1 = 2 ^ k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ, mul_comm]
  have h := ComputableTidilyInO.iterate hh (ComputableTidilyInO.const 1) hdouble
    (R := fun x => 2 * 2 ^ h x) (Q := fun x => 2 * 2 ^ h x) (B := fun x => 2 ^ h x)
    (fun x k hk => by
      simp only [hiter, encUnary_apply, List.length_replicate]
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
      omega)
    (fun x k hk => by
      simp only [hiter, encUnary_apply, List.length_replicate]
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
      omega)
    (fun x k hk => by
      simp only [hiter, encUnary_apply, List.length_replicate]
      exact Nat.pow_le_pow_right (by norm_num) hk)
  exact h.of_enc_eq fun x => by rw [hiter]

namespace OV

/-- The states of the stream of vectors: a formula, a list of variables, and the number of the
next assignment. -/
abbrev StreamState : Type := (CNF ℕ × List ℕ) × ℕ

/-- Stream states encoded as framed tuples. -/
abbrev encStreamState : StreamState ↪ List Bool := encPair (encPair encCNF (encList encNat)) encNat

open ComputableTidilyInPolyTime in
/-- Computing the vector of a numbered assignment is polynomial-time. -/
theorem computableInPolyTime_clauseVector :
    ComputableInPolyTime (fun s : StreamState => clauseVector s.1.1 s.1.2 s.2)
      encStreamState encBits := by
  have e : (fun s : StreamState => clauseVector s.1.1 s.1.2 s.2) = fun s => s.1.1.map fun c =>
      !(c.any fun l => decide (s.1.2.idxOf l.1 < s.1.2.length) &&
        s.2.bits.getD (s.1.2.idxOf l.1) false == l.2) := by
    funext s
    simp only [clauseVector, satisfiesOn, bitsAssignment_eq_getD, List.idxOf_lt_length_iff]
  rw [e]
  refine .of_tidy ?_
  unfold encStreamState encCNF
  fun_prop

private theorem stream_bound {cF a S P b k C : ℕ} (hs : S ≤ b) (hP : b + 1 ≤ P)
    (ha : a + cF + 1 ≤ C) : cF * (S + 1) + k * (a * P) + b + 1 ≤ C * ((k + 1) * P + 1) := by
  have h₁ : cF * (S + 1) ≤ cF * P := Nat.mul_le_mul_left _ (by omega)
  have h₂ : k * (a * P) = a * (k * P) := by ring
  have h₃ : C * ((k + 1) * P + 1) = C * (k * P) + C * P + C := by ring
  have h₄ : a * (k * P) ≤ C * (k * P) := Nat.mul_le_mul_right _ (by omega)
  have h₅ : (cF + 1) * P ≤ C * P := Nat.mul_le_mul_right _ (by omega)
  have h₆ : (cF + 1) * P = cF * P + P := by ring
  omega

private theorem stream_space_bound {cF a S P b k C : ℕ} (hs : S ≤ b) (hP : b + 1 ≤ P)
    (ha : a + cF + 1 ≤ C) : cF * (S + 1) + a * P + b + 1 ≤ C * ((k + 1) * P + 1) := by
  have h₁ : cF * (S + 1) ≤ cF * P := Nat.mul_le_mul_left _ (by omega)
  have h₃ : C * ((k + 1) * P + 1) = C * (k * P) + C * P + C := by ring
  have h₅ : (a + cF + 1) * P ≤ C * P := Nat.mul_le_mul_right _ ha
  have h₆ : (a + cF + 1) * P = a * P + cF * P + P := by ring
  omega

private theorem iterate_next (s : StreamState) (i : ℕ) :
    (fun s : StreamState => (s.1, s.2 + 1))^[i] s = (s.1, s.2 + i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, Nat.add_assoc]

/-- **Streaming the vectors of a half of the variables**: the vectors of the `2 ^ |half φ|`
assignments numbered on `half φ`, each wrapped by `wrap`, followed by `fin`, are written within
time `2 ^ |half φ|` times a polynomial in the length of the encoded formula. -/
theorem exists_computableInO_stream {half : CNF ℕ → List ℕ}
    (hhalf : ComputableInPolyTime half encCNF (encList encNat))
    (hlen : ∀ φ, (half φ).length ≤ (encCNF φ).length)
    {wrap : List Bool → List Bool} (hwrap : ComputableInPolyTime wrap encBits encBits)
    (fin : List Bool) :
    ∃ e, ComputableInO (fun φ => ((halfVectors φ (half φ)).map wrap).flatten ++ fin) encCNF
      encBits (fun φ => 2 ^ (half φ).length * ((encCNF φ).length + 1) ^ e)
      fun φ => 2 ^ (half φ).length * ((encCNF φ).length + 1) ^ e := by
  have hhalf := hhalf.tidy
  have hwrap := hwrap.tidy
  have this : ∃ e, ComputableTidilyInO (fun φ => ((halfVectors φ (half φ)).map wrap).flatten ++ fin)
      encCNF encBits (fun φ => 2 ^ (half φ).length * ((encCNF φ).length + 1) ^ e) fun φ => 2 ^
      (half φ).length * ((encCNF φ).length + 1) ^ e := by
    -- the rounds
    obtain ⟨dN, _, ⟨tN, sN, ⟨cN, htN⟩, ⟨cN', hsN⟩, hN⟩, _⟩ :=
      (show ComputableTidilyInPolyTime (fun s : StreamState => (s.1, s.2 + 1)) encStreamState
        encStreamState by fun_prop).exists_degree
    obtain ⟨dE, _, ⟨tE, sE, ⟨cE, htE⟩, ⟨cE', hsE⟩, hE⟩, _⟩ :=
      (hwrap.comp computableInPolyTime_clauseVector.tidy).exists_degree
    obtain ⟨cF, hF⟩ :=
      ComputableTidilyInLinearTimeAndSpace.const (encIn := encStreamState) (encMid := encBits) fin
    set D := dN + dE + 1
    set B : StreamState × ℕ → ℕ := fun x =>
      2 * (encPair encCNF (encList encNat) x.1.1).length + 1 + (encNat (x.1.2 + x.2)).length
    have hstate : ∀ x : StreamState × ℕ, ∀ i ≤ x.2,
        (encStreamState ((fun s : StreamState => (s.1, s.2 + 1))^[i] x.1)).length ≤ B x := by
      intro x i hi
      rw [iterate_next]
      have := ComputableTidilyInO.length_encNat_mono (show x.1.2 + i ≤ x.1.2 + x.2 by omega)
      simp only [encStreamState, length_encPair, B] at this ⊢
      omega
    have hpowN (x : StreamState × ℕ) (s : StreamState) (hs : (encStreamState s).length ≤ B x) :
        (encStreamState s).length + 1 ≤ (B x + 1) := by omega
    have hD (x : StreamState × ℕ) (d : ℕ) (hd : d ≤ D) : (B x + 1) ^ d ≤ (B x + 1) ^ D :=
      Nat.pow_le_pow_right (Nat.succ_pos _) hd
    obtain ⟨c, h⟩ := hN.iterate_unary_stream_sum hE hF
      (R := fun x _ => (cN + cE + 3) * (B x + 1) ^ D) (Q := fun x => (cN' + cE') * (B x + 1) ^ D)
      (B := B)
      (fun x i hi => by
        have h₁ := hstate x i hi.le
        have h₂ := hstate x (i + 1) hi
        have h₃ := (htN ((fun s : StreamState => (s.1, s.2 + 1))^[i] x.1)).trans
          (Nat.mul_le_mul_left cN ((Nat.pow_le_pow_left (hpowN x _ h₁) dN).trans
            (hD x dN (by omega))))
        have h₄ := (htE ((fun s : StreamState => (s.1, s.2 + 1))^[i] x.1)).trans
          (Nat.mul_le_mul_left cE ((Nat.pow_le_pow_left (hpowN x _ h₁) dE).trans
            (hD x dE (by omega))))
        have h₅ : B x + 1 ≤ (B x + 1) ^ D := Nat.le_self_pow (by omega) _
        nlinarith)
      (fun x i hi => by
        have h₁ := hstate x i hi.le
        have h₃ := (hsN ((fun s : StreamState => (s.1, s.2 + 1))^[i] x.1)).trans
          (Nat.mul_le_mul_left cN' ((Nat.pow_le_pow_left (hpowN x _ h₁) dN).trans
            (hD x dN (by omega))))
        have h₄ := (hsE ((fun s : StreamState => (s.1, s.2 + 1))^[i] x.1)).trans
          (Nat.mul_le_mul_left cE' ((Nat.pow_le_pow_left (hpowN x _ h₁) dE).trans
            (hD x dE (by omega))))
        nlinarith)
      hstate
    -- the stream, within `O((k + 1) (B x + 1) ^ D)` for `k` rounds
    have hsum (x : StreamState × ℕ) : ∑ i ∈ Finset.range x.2, (cN + cE + 3) * (B x + 1) ^ D =
        x.2 * ((cN + cE + 3) * (B x + 1) ^ D) := by simp
    have hB1 (x : StreamState × ℕ) : B x + 1 ≤ (B x + 1) ^ D := Nat.le_self_pow (by omega) _
    have hstream : ComputableTidilyInO (fun x : StreamState × ℕ =>
        ((List.range x.2).map fun i => wrap (clauseVector x.1.1.1 x.1.1.2 (x.1.2 + i))).flatten ++
          fin)
        (encPair encStreamState encUnary) encBits (fun x => (x.2 + 1) * (B x + 1) ^ D)
        fun x => (x.2 + 1) * (B x + 1) ^ D := by
      refine (ComputableTidilyInO.of_bounds h (c * (cF + cN + cE + cN' + cE' + 6)) (fun x => ?_)
        (fun x => ?_) (fun x => ?_)).of_enc_eq fun x => ?_
      · have hs := hstate x x.2 le_rfl
        rw [hsum, Nat.mul_assoc]
        exact Nat.mul_le_mul_left c (stream_bound hs (hB1 x) (by omega))
      · have hs := hstate x x.2 le_rfl
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left c (stream_space_bound hs (hB1 x) (by omega))
      · refine (h.length_le x).trans ?_
        have hs := hstate x x.2 le_rfl
        rw [hsum, Nat.mul_assoc]
        exact Nat.mul_le_mul_left c (stream_bound hs (hB1 x) (by omega))
      · simp only [iterate_next, Function.comp_apply, encBits_apply]
    -- the start of the stream: the state and the number of rounds in unary
    obtain ⟨d₀, _, hp₀⟩ := (show ComputableTidilyInPolyTime (fun φ : CNF ℕ => ((φ, half φ), 0))
      encCNF encStreamState by fun_prop).exists_degree
    obtain ⟨d₁, _, hp₁⟩ :=
      ((ComputableInPolyTime.length_list_binary encNat).tidy.comp hhalf).exists_degree
    have h := hstream.comp (hp₀.inO.prod (unary_two_pow hp₁.inO))
    -- the bounds
    obtain ⟨cv, dv, hV⟩ := hhalf.polyBounded_length.exists_le
    set Bb : CNF ℕ → ℕ := fun φ => (2 * cv + 8) * ((encCNF φ).length + 1) ^ (dv + 1)
    have hBb (φ : CNF ℕ) : B (((φ, half φ), 0), 2 ^ (half φ).length) ≤ Bb φ := by
      have h₁ := hV φ
      have h₂ := hlen φ
      have h₃ : (encCNF φ).length + 1 ≤ ((encCNF φ).length + 1) ^ (dv + 1) :=
        Nat.le_self_pow (by omega) _
      have h₄ : ((encCNF φ).length + 1) ^ dv ≤ ((encCNF φ).length + 1) ^ (dv + 1) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ dv)
      have h₅ := Nat.mul_le_mul_left cv h₄
      simp only [B, Bb, length_encPair, Nat.zero_add, encNat_two_pow, List.length_append,
        List.length_replicate, List.length_singleton] at h₁ h₂ h₃ h₅ ⊢
      nlinarith
    have hBbP : PolyBounded (fun φ => (encCNF φ).length) Bb :=
      .of_forall_le (2 * cv + 8) (dv + 1) fun φ => le_rfl
    have hL (j : ℕ) : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
        fun φ => ((encCNF φ).length + 1) ^ j := .of_forall_le 1 j fun φ => by simp
    have hL₁ : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) fun φ => (encCNF φ).length + 1 :=
      .of_forall_le 1 1 fun φ => by simp
    have hP : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
        fun φ => 2 * ((Bb φ + 1) ^ D + 3 * ((encCNF φ).length + 1)) :=
      (PolyBounded.const 2).mul
        ((((PolyBounded.of_polynomiallyBounded id (bound := fun x => (x + 1) ^ D)
          (by fun_prop)).comp hBbP).mono fun φ => le_rfl).add ((PolyBounded.const 3).mul hL₁))
    have hQ : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
        fun φ => 2 * (((encCNF φ).length + 1) ^ d₀ + ((encCNF φ).length + 1) ^ d₁ +
          ((encCNF φ).length + 1) + ((encCNF φ).length + 1) ^ 3) :=
      (PolyBounded.const 2).mul ((((hL d₀).add (hL d₁)).add hL₁).add (hL 3))
    obtain ⟨c, e, hT⟩ := exists_le_mul_two_pow_of_polyBounded (μ := fun φ => (half φ).length)
      (T := fun φ => ((encCNF φ).length + 1) ^ d₀ + (((encCNF φ).length + 1) ^ d₁ +
          (encCNF φ).length + ((half φ).length + 1) * (2 * 2 ^ (half φ).length +
            2 ^ (half φ).length + ((encNat (half φ).length).length + 1) ^ 2)) +
          (2 ^ (half φ).length + 1) * (B (((φ, half φ), 0), 2 ^ (half φ).length) + 1) ^ D +
        (((encCNF φ).length + 1) ^ d₀ + (((encCNF φ).length + 1) ^ d₁ + (encCNF φ).length +
          2 * 2 ^ (half φ).length + 2 ^ (half φ).length + (encNat (half φ).length).length) +
          (2 ^ (half φ).length + 1) * (B (((φ, half φ), 0), 2 ^ (half φ).length) + 1) ^ D))
      hP hQ fun φ => by
        have h₁ := Nat.mul_le_mul_left (2 ^ (half φ).length + 1)
          (Nat.pow_le_pow_left (Nat.add_le_add_right (hBb φ) 1) D)
        have h₂ := hlen φ
        have h₃ := (Universal.length_encNat_le (half φ).length).trans h₂
        have h₄ : ((half φ).length + 1) * ((encNat (half φ).length).length + 1) ^ 2 ≤
            ((encCNF φ).length + 1) ^ 3 := by
          rw [pow_succ' _ 2]
          exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
        have h₇ : (encCNF φ).length + 1 ≤ ((encCNF φ).length + 1) ^ 3 := Nat.le_self_pow (by omega)
          _
        generalize (B (((φ, half φ), 0), 2 ^ (half φ).length) + 1) ^ D = X at h₁ ⊢
        generalize (Bb φ + 1) ^ D = Y at h₁ ⊢
        generalize ((encNat (half φ).length).length + 1) ^ 2 = K₂ at h₄ ⊢
        generalize (encNat (half φ).length).length = K at h₃ ⊢
        generalize ((encCNF φ).length + 1) ^ 3 = L₃ at h₄ h₇ ⊢
        generalize ((encCNF φ).length + 1) ^ d₀ = L₀
        generalize ((encCNF φ).length + 1) ^ d₁ = L₁
        generalize 2 ^ (half φ).length = N at h₁ ⊢
        generalize (encCNF φ).length = L at h₂ h₃ h₇ ⊢
        generalize (half φ).length = n at h₂ h₄ ⊢
        have h₆ : (n + 1) * (3 * N) ≤ (N + 1) * (3 * (L + 1)) :=
          calc (n + 1) * (3 * N) ≤ (L + 1) * (3 * (N + 1)) :=
                Nat.mul_le_mul (by omega) (by omega)
            _ = (N + 1) * (3 * (L + 1)) := by ring
        have h₈ : 3 * N ≤ (N + 1) * (3 * (L + 1)) := by nlinarith
        have e₁ : (n + 1) * (2 * N + N + K₂) = (n + 1) * (3 * N) + (n + 1) * K₂ := by ring
        have e₂ : (N + 1) * (2 * (Y + 3 * (L + 1))) = 2 * ((N + 1) * Y) +
            2 * ((N + 1) * (3 * (L + 1))) := by ring
        omega
    refine ⟨e, (h.mono c (fun φ => ?_) fun φ => ?_).of_enc_eq fun φ => ?_⟩
    all_goals try
      have := hT φ
      have e : c * (2 ^ (half φ).length * ((encCNF φ).length + 1) ^ e + 1) =
        c * 2 ^ (half φ).length * ((encCNF φ).length + 1) ^ e + c := by ring
      simp only [Function.comp_apply] at this ⊢
      omega
    simp [halfVectors, Function.comp_def]
  simpa only
    [computableInPolyTime_iff_computableTidilyInPolyTime, computableInO_iff_computableTidilyInO]
    using this

attribute [local fun_prop] ComputableInPolyTime.tidy in
open ComputableTidilyInPolyTime in
theorem computableInPolyTime_firstVars :
    ComputableInPolyTime firstVars encCNF (encList encNat) := by
  have hvars := SAT.computableInPolyTime_distinctVars.tidy
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime (fun φ => (φ.distinctVars.reverse.drop
      (φ.distinctVars.length - φ.distinctVars.length / 2)).reverse)
      encCNF (encList encNat) :=
    (listReverse encNat).comp ((dropUnary (encA := encNat)).comp
      (((listReverse encNat).comp SAT.computableInPolyTime_distinctVars.tidy).prod
        (show ComputableTidilyInPolyTime (fun φ => φ.distinctVars.length -
          φ.distinctVars.length / 2) encCNF encUnary by fun_prop)))
  have h' : ComputableTidilyInPolyTime (fun φ => φ.distinctVars.take
      (φ.distinctVars.length / 2)) encCNF (encList encNat) := by
    simpa only [← List.reverse_take, List.reverse_reverse] using h
  exact h'

attribute [local fun_prop] ComputableInPolyTime.tidy in
open ComputableTidilyInPolyTime in
theorem computableInPolyTime_secondVars :
    ComputableInPolyTime secondVars encCNF (encList encNat) := by
  have hvars := SAT.computableInPolyTime_distinctVars.tidy
  refine .of_tidy ?_
  exact (dropUnary (encA := encNat)).comp (SAT.computableInPolyTime_distinctVars.tidy.prod
    (show ComputableTidilyInPolyTime (fun φ => φ.distinctVars.length / 2) encCNF
      encUnary by fun_prop))

theorem length_firstVars_le (φ : CNF ℕ) : (firstVars φ).length ≤ (encCNF φ).length := by
  rw [length_firstVars]
  exact (Nat.div_le_self _ _).trans (φ.numVars_le_length_vars.trans (SAT.length_vars_le φ))

theorem length_secondVars_le (φ : CNF ℕ) : (secondVars φ).length ≤ (encCNF φ).length := by
  rw [length_secondVars]
  exact (Nat.sub_le _ _).trans (φ.numVars_le_length_vars.trans (SAT.length_vars_le φ))

end OV

open ComputableTidilyInPolyTime in
/-- **The split-and-list reduction is fast**: it writes its output within time `2 ^ ⌈n / 2⌉` times
a polynomial in the length of the encoded formula, on formulas with `n` variables. -/
theorem exists_computableInO_toOV : ∃ e, ComputableInO toOV encCNF encOV
    (fun φ => 2 ^ (φ.numVars - φ.numVars / 2) * ((encCNF φ).length + 1) ^ e)
    fun φ => 2 ^ (φ.numVars - φ.numVars / 2) * ((encCNF φ).length + 1) ^ e := by
  have this : ∃ e, ComputableTidilyInO toOV encCNF encOV
      (fun φ => 2 ^ (φ.numVars - φ.numVars / 2) * ((encCNF φ).length + 1) ^ e) fun φ => 2 ^
      (φ.numVars - φ.numVars / 2) * ((encCNF φ).length + 1) ^ e := by
    obtain ⟨e₁, h₁⟩ := OV.exists_computableInO_stream OV.computableInPolyTime_firstVars
      OV.length_firstVars_le (wrap := fun v => ((frame v).map fun b => [true, b]).flatten)
      (by fun_prop) [false]
    obtain ⟨e₂, h₂⟩ := OV.exists_computableInO_stream OV.computableInPolyTime_secondVars
      OV.length_secondVars_le (wrap := frame) (.of_tidy (bitsFrame encBits)) []
    have hfm (l : List (List Bool)) (g : Bool → List Bool) :
        l.flatten.flatMap g = (l.map (·.flatMap g)).flatten := by
      induction l with
      | nil => rfl
      | cons a l ih => simp [List.flatMap_append, ih]
    have hencList (L : List (List Bool)) : encList encBits L = (L.map frame).flatten := by
      induction L with
      | nil => rfl
      | cons v L ih => rw [encList_cons, ih]; rfl
    have h := h₁.tidy.append h₂.tidy (g := toOV) (encOut := encOV) fun φ => by
      rw [encOV, encPair_apply, hencList, hencList]
      simp only [toOV, encBits_apply, List.append_nil]
      rw [frame, hfm, List.map_map]
      rfl
    refine ⟨e₁ + e₂, h.mono 2 (fun φ => ?_) fun φ => ?_⟩ <;>
    · simp only [OV.length_firstVars, OV.length_secondVars]
      have h₁ : 2 ^ (φ.numVars / 2) ≤ 2 ^ (φ.numVars - φ.numVars / 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h₂ : ((encCNF φ).length + 1) ^ e₁ ≤ ((encCNF φ).length + 1) ^ (e₁ + e₂) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
      have h₃ : ((encCNF φ).length + 1) ^ e₂ ≤ ((encCNF φ).length + 1) ^ (e₁ + e₂) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
      have := Nat.mul_le_mul h₁ h₂
      have := Nat.mul_le_mul_left (2 ^ (φ.numVars - φ.numVars / 2)) h₃
      nlinarith
  simpa only [computableInO_iff_computableTidilyInO] using this


/-! ### Williams' theorem -/

/-- **Williams' theorem** [Williams2005]: a decider for `OV` within time `N ^ (2 - ε)` times a
polynomial in the dimension, on instances of `N` vectors, gives a decider for `SAT` within time
`2 ^ ((1 - ε / 2) n)` times a polynomial in the length of the encoded formula, on formulas with `n`
variables, for `0 < ε ≤ 1`; for `ε > 1` it gives the exponent `1 / 2` of the reduction. -/
theorem DecidableInTimeO.decidableInExpTime_SAT {ε : ℝ} (hε : 0 < ε) {e : ℕ}
    (h : DecidableInTimeO OV encOV
      fun p => ((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε) * (OV.dim p + 1) ^ e) :
    DecidableInExpTime SAT encCNF CNF.numVars (1 - min ε 1 / 2) := by
  obtain ⟨g, t, c, hg, hgOV, ht⟩ := h.exists_computableInO
  have hg := hg.tidy
  obtain ⟨E, hred⟩ := exists_computableInO_toOV
  refine DecidableInExpTime.of_computableInO (.of_tidy (hg.comp hred.tidy)) (fun φ => by
    rw [← toOV_mem_OV_iff]
    exact hgOV _) (3 + 9 * c) (E + e) fun φ => ?_
  set ε₀ := min ε 1
  have hε₀ : 0 < ε₀ := lt_min hε one_pos
  have hε₁ : ε₀ ≤ 1 := min_le_right ε 1
  have hL : (1 : ℝ) ≤ ((encCNF φ).length : ℝ) + 1 := by
    linarith [(Nat.cast_nonneg (encCNF φ).length : (0 : ℝ) ≤ _)]
  set X : ℝ := 2 ^ ((1 - ε₀ / 2) * φ.numVars)
  have hn : (0 : ℝ) ≤ φ.numVars := Nat.cast_nonneg _
  have hX : (1 : ℝ) ≤ X := Real.one_le_rpow (by norm_num) (by nlinarith)
  -- the second half has at most `(n + 1) / 2` variables
  have hh₂ : ((φ.numVars - φ.numVars / 2 : ℕ) : ℝ) ≤ (φ.numVars + 1) / 2 := by
    have : 2 * (φ.numVars - φ.numVars / 2) ≤ φ.numVars + 1 := by omega
    have : (2 * (φ.numVars - φ.numVars / 2 : ℕ) : ℝ) ≤ φ.numVars + 1 := by exact_mod_cast this
    linarith
  have hpow (a : ℝ) (ha : 0 ≤ a) (hb : a * ((φ.numVars + 1) / 2) ≤ (1 - ε₀ / 2) * φ.numVars + 1) :
      (2 : ℝ) ^ (a * (φ.numVars - φ.numVars / 2 : ℕ)) ≤ 2 * X := by
    calc (2 : ℝ) ^ (a * (φ.numVars - φ.numVars / 2 : ℕ)) ≤ 2 ^ ((1 - ε₀ / 2) * φ.numVars + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            ((mul_le_mul_of_nonneg_left hh₂ ha).trans hb)
      _ = 2 * X := by rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
  -- the reduction
  have hT₁ : ((2 ^ (φ.numVars - φ.numVars / 2) * ((encCNF φ).length + 1) ^ E : ℕ) : ℝ) ≤
      2 * X * (((encCNF φ).length : ℝ) + 1) ^ E := by
    push_cast
    have := hpow 1 zero_le_one (by nlinarith)
    rw [one_mul, Real.rpow_natCast] at this
    exact mul_le_mul_of_nonneg_right this (by positivity)
  -- the decider on the reduced instance
  have hN : ((toOV φ).1.length + (toOV φ).2.length : ℕ) ≤ 2 * 2 ^ (φ.numVars - φ.numVars / 2) := by
    rw [length_toOV_fst, length_toOV_snd]
    have : 2 ^ (φ.numVars / 2) ≤ 2 ^ (φ.numVars - φ.numVars / 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hN₁ : (1 : ℝ) ≤ ((toOV φ).1.length + (toOV φ).2.length : ℕ) := by
    rw [length_toOV_fst]
    exact_mod_cast Nat.one_le_two_pow.trans (Nat.le_add_right _ _)
  have hpowN : (((toOV φ).1.length + (toOV φ).2.length : ℕ) : ℝ) ^ (2 - ε) ≤ 8 * X := by
    calc (((toOV φ).1.length + (toOV φ).2.length : ℕ) : ℝ) ^ (2 - ε)
        ≤ (((toOV φ).1.length + (toOV φ).2.length : ℕ) : ℝ) ^ (2 - ε₀) :=
          Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith [min_le_left ε 1])
      _ ≤ ((2 * 2 ^ (φ.numVars - φ.numVars / 2) : ℕ) : ℝ) ^ (2 - ε₀) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by linarith)
      _ = 2 ^ (2 - ε₀) * 2 ^ ((2 - ε₀) * (φ.numVars - φ.numVars / 2 : ℕ)) := by
          push_cast
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num), mul_comm ((φ.numVars - φ.numVars / 2 : ℕ) : ℝ)]
      _ ≤ 4 * (2 * X) := by
          refine mul_le_mul ?_ (hpow _ (by linarith) ?_) (by positivity) (by norm_num)
          · calc (2 : ℝ) ^ (2 - ε₀) ≤ 2 ^ (2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 4 := by norm_num
          · nlinarith
      _ = 8 * X := by ring
  have hdim : ((OV.dim (toOV φ) : ℝ) + 1) ^ e ≤ (((encCNF φ).length : ℝ) + 1) ^ e := by
    refine pow_le_pow_left₀ (by positivity) ?_ e
    have := (OV.dim_toOV_le φ).trans
      (length_le_length_encList (encList (encPair encNat encBool)) φ)
    have : (OV.dim (toOV φ) : ℝ) ≤ (encCNF φ).length := by exact_mod_cast this
    linarith
  have hT₂ : (t (toOV φ) : ℝ) ≤ c * (8 * X * (((encCNF φ).length : ℝ) + 1) ^ e) + c := by
    refine (ht (toOV φ)).trans ?_
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have := mul_le_mul hpowN hdim (by positivity) (by positivity)
    nlinarith
  -- together
  have hE : (((encCNF φ).length : ℝ) + 1) ^ E ≤ (((encCNF φ).length : ℝ) + 1) ^ (E + e) :=
    pow_le_pow_right₀ hL (Nat.le_add_right E e)
  have he : (((encCNF φ).length : ℝ) + 1) ^ e ≤ (((encCNF φ).length : ℝ) + 1) ^ (E + e) :=
    pow_le_pow_right₀ hL (Nat.le_add_left e E)
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hY : (1 : ℝ) ≤ X * (((encCNF φ).length : ℝ) + 1) ^ (E + e) :=
    one_le_mul_of_one_le_of_one_le hX (one_le_pow₀ hL)
  have h₁ := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 2 * X)
  have h₂ := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ c * (8 * X))
  have h₃ := mul_le_mul_of_nonneg_left hY hc
  rw [Nat.cast_add, show ((3 + 9 * c : ℕ) : ℝ) = 3 + 9 * (c : ℝ) by push_cast; ring]
  nlinarith

/-- **The strong exponential time hypothesis implies the orthogonal vectors hypothesis**
[Williams2005]. -/
theorem OVH_of_SETH (h : SETH) : OVH := by
  intro ε hε e hOV
  have hSAT := hOV.decidableInExpTime_SAT hε
  have hδ : 0 < min ε 1 / 2 := half_pos (lt_min hε one_pos)
  obtain ⟨k, hk⟩ := h _ hδ
  refine hk ?_
  rw [KSAT_eq_inter k (KSAT_subset_SAT k) le_rfl]
  refine hSAT.inter (computableInPolyTime_all_length_le k) ?_
  have : min ε 1 / 2 ≤ 1 / 2 := div_le_div_of_nonneg_right (min_le_right ε 1) zero_le_two
  linarith

end Cslib.Complexity
