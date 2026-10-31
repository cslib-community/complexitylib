/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.BoundedQuery
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Complexity.Classes.Sparse.Turing
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Kadin's theorem: sparse Turing-complete sets for `NP`

If `NP` has a sparse polynomial-time Turing-complete set, that is a sparse `S ∈ NP` to which
`SAT` is polynomial-time Turing reducible, then the polynomial hierarchy collapses to
`P^{NP[O(log n)]}` [Kadin][Kadin1989] [Hemaspaandra and Ogihara, Theorem 1.14][HemaspaandraOgihara2002].

The proof follows the census argument of [Hemaspaandra and Ogihara, Theorem 1.14]
[HemaspaandraOgihara2002]. The census of `S` up to length `m` is the number of members of `S` of
length at most `m`; it is polynomial in `m` because `S` is sparse.

* With `S ∈ NP`, "the census is at least `k`" is a problem in `NP`: guess `k` distinct members,
  each with its certificate. Binary search finds the exact census with `O(log n)` such requests.
* Given the exact census `k`, a list of `k` distinct short members of `S` lists them all
  (`Cslib.Complexity.mem_iff_of_length_eq_length_shortMembers`), so it can replace the oracle `S`
  (`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle_bool`). Hence one more
  request in `NP`, which guesses the list and a first certificate, decides a problem in `Σ₂`.

So `Σ₂ ⊆ P^{NP[O(log n)]}`. The Companion completes the proof by `Θ₂ ⊆ Σ₂ ∩ Π₂` and closure of
`Θ₂` under complement; here `PH = Σ₂` comes instead from the sparse form of the Karp–Lipton
theorem (`Cslib.Complexity.PH_eq_SigmaP_two_of_SAT_mem_PWithOracle`).

## Main definitions

* `Cslib.Complexity.KadinCensus.language`: the `NP` problem asked by the algorithm, on triples
  `(a, k, b)`: `k` distinct short members of `S` exist, and if `b`, they also witness the first
  quantifier of a `Σ₂` problem.

## Main results

* `Cslib.Complexity.length_le_length_shortMembers`,
  `Cslib.Complexity.mem_iff_of_length_eq_length_shortMembers`: the census bounds the duplicate-free
  lists of short members, and a list attaining it lists them all.
* `Cslib.Complexity.KadinCensus.mem_language_false_iff`,
  `Cslib.Complexity.KadinCensus.mem_language_census_true_iff`: the meaning of the requests.
* `Cslib.Complexity.KadinCensus.language_mem_NP`: the requests form a problem in `NP`.

## References

* [J. Kadin, *P^{NP[O(log n)]} and sparse Turing-complete sets for NP*][Kadin1989]
* [L. A. Hemaspaandra, M. Ogihara, *The Complexity Theory Companion*][HemaspaandraOgihara2002]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {S : Set (List Bool)}

/-! ### The census -/

theorem nodup_shortMembers (S : Set (List Bool)) (n : ℕ) : (shortMembers S n).Nodup :=
  Finset.nodup_toList _

/-- **The census bounds the lists of distinct short members.** -/
theorem length_le_length_shortMembers {ℓ : List (List Bool)} {n : ℕ} (hnd : ℓ.Nodup)
    (h : ∀ s ∈ ℓ, s ∈ S ∧ s.length ≤ n) : ℓ.length ≤ (shortMembers S n).length := by
  rw [← List.toFinset_card_of_nodup hnd, ← List.toFinset_card_of_nodup (nodup_shortMembers S n)]
  exact Finset.card_le_card fun s hs => by
    rw [List.mem_toFinset] at hs ⊢
    exact mem_shortMembers.mpr (h s hs)

/-- **A list attaining the census lists all short members.** A duplicate-free list of short
members of `S` with as many entries as there are short members agrees with `S` on every short
word. -/
theorem mem_iff_of_length_eq_length_shortMembers {ℓ : List (List Bool)} {n : ℕ} (hnd : ℓ.Nodup)
    (h : ∀ s ∈ ℓ, s ∈ S ∧ s.length ≤ n) (hlen : ℓ.length = (shortMembers S n).length)
    {s : List Bool} (hs : s.length ≤ n) : s ∈ ℓ ↔ s ∈ S := by
  have hsub : ℓ.toFinset ⊆ (shortMembers S n).toFinset := fun t ht => by
    rw [List.mem_toFinset] at ht ⊢
    exact mem_shortMembers.mpr (h t ht)
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup (nodup_shortMembers S n),
      hlen])
  refine ⟨fun hsℓ => (h s hsℓ).1, fun hsS => ?_⟩
  have hmem : s ∈ (shortMembers S n).toFinset :=
    List.mem_toFinset.mpr (mem_shortMembers.mpr ⟨hsS, hs⟩)
  rwa [← heq, List.mem_toFinset] at hmem

/-- The census of a sparse language is polynomially bounded. -/
theorem exists_length_shortMembers_le (hS : S ∈ SPARSE encBits) :
    ∃ c d : ℕ, ∀ n, (shortMembers S n).length ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hcard⟩ := exists_card_le_of_mem_SPARSE hS
  refine ⟨c, d, fun n => ?_⟩
  unfold shortMembers
  rw [Finset.length_toList]
  exact hcard n _ fun w hw => by simpa using hw

/-! ### The requests -/

namespace KadinCensus

variable (S) (enc : α ↪ List Bool) (m p : Polynomial ℕ)
  (G : (α × List Bool) × List (List Bool) → Bool)

/-- A guess for the request `(a, k, b)`: `ℓ` lists `k` distinct members of `S` of length at most
`m |enc a|`, and if `b`, some word `w` of length `p |enc a|` has `G ((a, w), ℓ) = false`. -/
def Guess (x : α × ℕ × Bool) (ℓ : List (List Bool)) : Prop :=
  ℓ.Nodup ∧ ℓ.length = x.2.1 ∧ (∀ s ∈ ℓ, s ∈ S ∧ s.length ≤ m.eval (enc x.1).length) ∧
    (x.2.2 = true → ∃ w : List Bool, w.length = p.eval (enc x.1).length ∧ G ((x.1, w), ℓ) = false)

/-- The requests that have a guess. -/
def language : Set (α × ℕ × Bool) := {x | ∃ ℓ, Guess S enc m p G x ℓ}

/-- The census of `S` up to the length `m |enc a|`. -/
noncomputable def census (a : α) : ℕ := (shortMembers S (m.eval (enc a).length)).length

variable {S enc m p G}

/-- **A request with `b = false` asks whether the census is at least `k`.** -/
theorem mem_language_false_iff {a : α} {k : ℕ} :
    (a, k, false) ∈ language S enc m p G ↔ k ≤ census S enc m a := by
  constructor
  · rintro ⟨ℓ, hnd, hlen, hmem, -⟩
    have hle := length_le_length_shortMembers hnd hmem
    rw [hlen] at hle
    exact hle
  · intro hk
    refine ⟨(shortMembers S (m.eval (enc a).length)).take k,
      (nodup_shortMembers _ _).sublist (List.take_sublist _ _),
      by rw [List.length_take]; exact Nat.min_eq_left hk, fun s hs => ?_,
      fun h => absurd h Bool.false_ne_true⟩
    exact mem_shortMembers.mp (List.mem_of_mem_take hs)

/-- **At the exact census, a request with `b = true` asks for the first quantifier.** If `G`
computes `g` whenever its list agrees with `S` on the words of length at most `m |enc a|`, the
request `(a, census, true)` asks whether some `w` of length `p |enc a|` has `g (a, w) = false`. -/
theorem mem_language_census_true_iff {a : α} {g : α × List Bool → Bool}
    (hG : ∀ w ℓ, w.length = p.eval (enc a).length →
      (∀ s : List Bool, s.length ≤ m.eval (enc a).length → (s ∈ ℓ ↔ s ∈ S)) →
        G ((a, w), ℓ) = g (a, w)) :
    (a, census S enc m a, true) ∈ language S enc m p G ↔
      ∃ w : List Bool, w.length = p.eval (enc a).length ∧ g (a, w) = false := by
  constructor
  · rintro ⟨ℓ, hnd, hlen, hmem, hw⟩
    obtain ⟨w, hwlen, hGw⟩ := hw rfl
    exact ⟨w, hwlen, (hG w ℓ hwlen fun s hs =>
      mem_iff_of_length_eq_length_shortMembers hnd hmem hlen hs) ▸ hGw⟩
  · rintro ⟨w, hwlen, hgw⟩
    refine ⟨shortMembers S (m.eval (enc a).length), nodup_shortMembers _ _, rfl,
      fun s hs => mem_shortMembers.mp hs, fun _ => ⟨w, hwlen, ?_⟩⟩
    rw [hG w _ hwlen fun s hs => by simp only [mem_shortMembers, hs, and_true]]
    exact hgw

/-! ### The requests are in `NP` -/

/-- A duplicate-free list is one in which no entry occurs twice, tested by counting. -/
theorem not_any_one_lt_countP_iff_nodup (l : List (List Bool)) :
    (!(l.any fun s => decide (1 < l.countP fun t => decide (t = s)))) = true ↔ l.Nodup := by
  have hc (s : List Bool) : (l.countP fun t => decide (t = s)) = l.count s := by
    rw [List.count_eq_countP]
    congr 1
    funext t
    rw [Bool.eq_iff_iff]
    simp
  simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq, not_lt, hc]
  rw [List.nodup_iff_count_le_one]
  refine ⟨fun h a => ?_, fun h a _ => h a⟩
  by_cases ha : a ∈ l
  · exact h a ha
  · rw [List.count_eq_zero_of_not_mem ha]
    omega

variable (enc m p G) in
/-- The check of a witness `(pairs, w)` for the request `(a, k, b)`: the first components of
`pairs` are `k` distinct words of length at most `m |enc a|`, each with an accepted certificate of
the verifier `VS` of `S`, and if `b`, `w` has length `p |enc a|` and `G ((a, w), ℓ) = false`. -/
def check (VS : List Bool × List Bool → Bool) (pS : Polynomial ℕ)
    (z : (α × ℕ × Bool) × (List (List Bool × List Bool) × List Bool)) : Bool :=
  !((z.2.1.map Prod.fst).any fun s =>
      decide (1 < (z.2.1.map Prod.fst).countP fun t => decide (t = s))) &&
    decide ((z.2.1.map Prod.fst).length = z.1.2.1) &&
    !(z.2.1.any fun sc => !(decide (sc.1.length ≤ m.eval (enc z.1.1).length) &&
      decide (sc.2.length = pS.eval sc.1.length) && VS sc)) &&
    (!z.1.2.2 || (decide (z.2.2.length = p.eval (enc z.1.1).length) &&
      !G ((z.1.1, z.2.2), z.2.1.map Prod.fst)))

theorem check_eq_true_iff {VS : List Bool × List Bool → Bool} {pS : Polynomial ℕ}
    {x : α × ℕ × Bool} {y : List (List Bool × List Bool) × List Bool} :
    check enc m p G VS pS (x, y) = true ↔
      (y.1.map Prod.fst).Nodup ∧ (y.1.map Prod.fst).length = x.2.1 ∧
        (∀ sc ∈ y.1, sc.1.length ≤ m.eval (enc x.1).length ∧
          sc.2.length = pS.eval sc.1.length ∧ VS sc = true) ∧
        (x.2.2 = true → y.2.length = p.eval (enc x.1).length ∧
          G ((x.1, y.2), y.1.map Prod.fst) = false) := by
  unfold check
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, not_any_one_lt_countP_iff_nodup,
    and_assoc, and_assoc]
  refine and_congr Iff.rfl (and_congr decide_eq_true_iff (and_congr ?_ ?_))
  · simp [List.any_eq_false, and_assoc]
  · cases x.2.2 <;> simp

/-- The witnesses: the certificates of `S` are read by its verifier `VS`. -/
theorem language_eq_setOf_check {VS : List Bool × List Bool → Bool} {pS : Polynomial ℕ}
    (hSV : IsVerifier encBits pS VS S) :
    language S enc m p G = {x | ∃ y, check enc m p G VS pS (x, y) = true} := by
  classical
  ext x
  simp only [Set.mem_ofPred_eq, check_eq_true_iff]
  constructor
  · rintro ⟨ℓ, hnd, hlen, hmem, hw⟩
    have hcert (s : List Bool) (hs : s ∈ S) :
        ∃ c, c.length = pS.eval s.length ∧ VS (s, c) = true := (hSV s).1 hs
    let cert : List Bool → List Bool := fun s => if hs : s ∈ S then (hcert s hs).choose else []
    have hmap : (ℓ.map fun s => (s, cert s)).map Prod.fst = ℓ := by
      rw [List.map_map]
      exact List.map_id' ℓ
    refine ⟨(ℓ.map fun s => (s, cert s),
      if h : x.2.2 = true then (hw h).choose else []), by rw [hmap]; exact hnd,
      by rw [hmap]; exact hlen, fun sc hsc => ?_, fun h => ?_⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsc
      have hsS := (hmem s hs).1
      simp only [cert, hsS, ↓reduceDIte]
      exact ⟨(hmem s hs).2, (hcert s hsS).choose_spec.1, (hcert s hsS).choose_spec.2⟩
    · simp only [h, ↓reduceDIte, hmap]
      exact (hw h).choose_spec
  · rintro ⟨⟨pairs, w⟩, hnd, hlen, hpairs, hw⟩
    refine ⟨pairs.map Prod.fst, hnd, hlen, fun s hs => ?_, fun h => ⟨w, hw h⟩⟩
    obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hlenS, hc, hV⟩ := hpairs sc hsc
    exact ⟨(hSV sc.1).2 ⟨sc.2, hc, hV⟩, hlenS⟩

/-- The check of a witness is polynomial-time. -/
theorem computableInPolyTime_check {VS : List Bool × List Bool → Bool} {pS : Polynomial ℕ}
    (hVS : ComputableInPolyTime VS (encPair encBits encBits) encBool)
    (hG : ComputableInPolyTime G (encPair (encPair enc encBits) (encList encBits)) encBool) :
    ComputableInPolyTime (check enc m p G VS pS)
      (encPair (encPair enc (encPair encUnary encBool))
        (encPair (encList (encPair encBits encBits)) encBits)) encBool := by
  unfold check
  fun_prop

/-- **The requests form a problem in `NP`** when `S` is a sparse problem in `NP` and `G` is
polynomial-time: a witness lists the guessed members with their certificates, and the word `w`.
Its length is polynomial because the census of `S` is. -/
theorem language_mem_NP (hS : S ∈ NP encBits) (hsparse : S ∈ SPARSE encBits)
    (hG : ComputableInPolyTime G (encPair (encPair enc encBits) (encList encBits)) encBool) :
    language S enc m p G ∈ NP (encPair enc (encPair encUnary encBool)) := by
  obtain ⟨pS, VS, hVS, hSV⟩ := mem_NP.mp hS
  obtain ⟨c, d, hcensus⟩ := exists_length_shortMembers_le hsparse
  rw [language_eq_setOf_check hSV]
  refine mem_NP_of_witness
    (p := 2 * (Polynomial.C c * (m + 1) ^ d * (4 * m + 2 * pS.comp m + 3)) + 1 + p)
    (Decoder.pair (Decoder.list (Decoder.pair .bits .bits)) .bits)
    (computableInPolyTime_check hVS hG) (fun _ _ => Iff.rfl) fun x y hy => ?_
  obtain ⟨hnd, hlen, hpairs, hw⟩ := check_eq_true_iff.mp hy
  set n := (enc x.1).length
  refine ⟨(y.1, if x.2.2 = true then y.2 else []), check_eq_true_iff.mpr
    ⟨hnd, hlen, hpairs, fun h => by simpa only [h, ↓reduceIte] using hw h⟩, ?_⟩
  -- the guessed words are distinct short members of `S`, so there are at most census many
  have hcount : y.1.length ≤ c * (m.eval n + 1) ^ d := by
    have hle := length_le_length_shortMembers (S := S) (n := m.eval n) hnd fun s hs => by
      obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hs
      obtain ⟨hlenS, hc, hV⟩ := hpairs sc hsc
      exact ⟨(hSV sc.1).2 ⟨sc.2, by rw [encBits_apply]; exact hc, hV⟩, hlenS⟩
    rw [List.length_map] at hle
    exact hle.trans (hcensus _)
  have hpair (sc : List Bool × List Bool) (hsc : sc ∈ y.1) :
      2 * (encPair encBits encBits sc).length + 1 ≤
        4 * m.eval n + 2 * pS.eval (m.eval n) + 3 := by
    obtain ⟨hlenS, hc, -⟩ := hpairs sc hsc
    have hpS : pS.eval sc.1.length ≤ pS.eval (m.eval n) := pS.eval_mono hlenS
    rw [length_encPair, encBits_apply, encBits_apply, hc]
    omega
  have hlist : (encList (encPair encBits encBits) y.1).length ≤
      c * (m.eval n + 1) ^ d * (4 * m.eval n + 2 * pS.eval (m.eval n) + 3) := by
    rw [length_encList]
    have h := List.sum_le_length_nsmul (y.1.map fun sc => 2 * (encPair encBits encBits sc).length + 1)
      (4 * m.eval n + 2 * pS.eval (m.eval n) + 3) fun z hz => by
        obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hz
        exact hpair sc hsc
    rw [List.length_map, smul_eq_mul] at h
    exact h.trans (Nat.mul_le_mul_right _ hcount)
  have hword : (if x.2.2 = true then y.2 else []).length ≤ p.eval n := by
    split_ifs with h
    · exact (hw h).1.le
    · exact Nat.zero_le _
  have hn : n ≤ (encPair enc (encPair encUnary encBool) x).length := length_le_encPair_left _ _ _
  refine le_trans ?_ (Polynomial.eval_mono _ hn)
  rw [length_encPair, encBits_apply]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_comp, Polynomial.eval_ofNat]
  omega

end KadinCensus

end Cslib.Complexity
