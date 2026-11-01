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
public import Complexity.Languages.Probabilistic.Iteration
import Complexity.Computability.Complexity.Classes.NP.Image
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Complexity.Classes.Oracle.ListOracle
import Complexity.Computability.Complexity.Classes.PH.Projection
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Foundations.Data.List.Counting
import Complexity.Foundations.Data.Nat.PolynomialBound.Log
import Complexity.Tactic.EncLen
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Kadin's theorem: sparse Turing-complete sets for `NP`

If `NP` has a sparse polynomial-time Turing-complete set, that is a sparse `S ∈ NP` to which
`SAT` is polynomial-time Turing reducible, then the polynomial hierarchy collapses to
`P^{NP[O(log n)]}` (`Cslib.Complexity.PH_subset_PNPLog_of_sparse`) [Kadin][Kadin1989]
[Hemaspaandra and Ogihara, Theorem 1.14][HemaspaandraOgihara2002].

The proof follows the census argument of [Hemaspaandra and Ogihara, Theorem 1.14]
[HemaspaandraOgihara2002]. The census of `S` up to length `m` is the number of members of `S` of
length at most `m`; it is polynomial in `m` because `S` is sparse.

* With `S ∈ NP`, "the census is at least `k`" is a problem in `NP`: guess `k` distinct members,
  each with its certificate. Binary search finds the exact census with `O(log n)` such requests.
* Given the exact census `k`, a list of `k` distinct short members of `S` lists them all
  (`Cslib.BitString.mem_iff_of_length_eq_length_shortMembers`), so it can replace the oracle `S`
  (`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle_bool`). Hence one more
  request in `NP`, which guesses the list and a first certificate, decides a problem in `Σ₂`.

So `Σ₂ ⊆ P^{NP[O(log n)]}`. The Companion completes the proof with `Θ₂ ⊆ Σ₂` and closure of `Θ₂`
under complement, which give `Σ₂ = Π₂`; here `PH = Σ₂` comes instead from the sparse form of the
Karp–Lipton theorem (`Cslib.Complexity.PH_eq_SigmaP_two_of_SAT_mem_PWithOracle`). The reverse
inclusion `P^{NP[O(log n)]} ⊆ PH`, which with this gives the Companion's `PH = Θ₂`, is not proved
here.

The hypothesis is the Turing-complete case. Kadin's abstract states the result for a sparse
`S ∈ NP` with `coNP ⊆ NP^S`, of which the Turing-complete case is a consequence; that form is not
formalized here.

The algorithm (`Cslib.Complexity.KadinCensus.program`) runs `⌈log₂ (N + 1)⌉` rounds of binary
search (`Cslib.Complexity.KadinCensus.searchStepProgram`) on an interval containing the census,
where `N` is the polynomial census bound, each round making one request to the encodings of the
satisfiable formulas through the Cook–Levin reduction, and then makes one last request. The loop
is certified by `Cslib.Probability.IsOraclePPTOn.iterateWith_spec'`; every reachable interval lies
in `[0, N]`.

## Main definitions

* `Cslib.Complexity.KadinCensus.language`: the `NP` problem asked by the algorithm, on triples
  `(a, k, finalQuery)`: `k` distinct short members of `S` exist, and if `finalQuery`, they also
  witness the first quantifier of a `Σ₂` problem.
* `Cslib.Complexity.KadinCensus.searchStep`: one round of binary search for a threshold.
* `Cslib.Complexity.KadinCensus.searchStepProgram`, `Cslib.Complexity.KadinCensus.program`: the
  oracle programs.

## Main results

* `Cslib.Complexity.KadinCensus.mem_language_false_iff`,
  `Cslib.Complexity.KadinCensus.mem_language_census_true_iff`: the meaning of the requests.
* `Cslib.Complexity.KadinCensus.language_mem_NP`: the requests form a problem in `NP`.
* `Cslib.Complexity.KadinCensus.fst_iterate_searchStep`: binary search finds the threshold.
* `Cslib.Complexity.KadinCensus.length_queriesWith_program_le`,
  `Cslib.Complexity.KadinCensus.isOraclePPTOn_program`: the algorithm makes one request per round
  plus one, and is strict oracle PPT.
* `Cslib.Complexity.SigmaP_two_subset_PNPLog_of_sparse`: `Σ₂ ⊆ P^{NP[O(log n)]}`.
* `Cslib.Complexity.PH_subset_PNPLog_of_sparse`: **Kadin's theorem**, `PH ⊆ P^{NP[O(log n)]}`.

## References

* [J. Kadin, *P^{NP[O(log n)]} and sparse Turing-complete sets for NP*][Kadin1989]
* [L. A. Hemaspaandra, M. Ogihara, *The Complexity Theory Companion*][HemaspaandraOgihara2002]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM BitString

variable {α : Type} {S : Set (List Bool)}

/-! ### The requests -/

namespace KadinCensus

variable (S) (enc : α ↪ List Bool) (m p : Polynomial ℕ)
  (G : (α × List Bool) × List (List Bool) → Bool)

/-- A guess for the request `(a, k, finalQuery)`: `ℓ` lists `k` distinct members of `S` of length
at most `m |enc a|`, and if `finalQuery`, some word `w` of length `p |enc a|` has
`G ((a, w), ℓ) = false`. -/
def Guess : α × ℕ × Bool → List (List Bool) → Prop
  | (a, k, finalQuery), ℓ =>
    ℓ.Nodup ∧ ℓ.length = k ∧ (∀ s ∈ ℓ, s ∈ S ∧ s.length ≤ m.eval (enc a).length) ∧
      (finalQuery = true →
        ∃ w : List Bool, w.length = p.eval (enc a).length ∧ G ((a, w), ℓ) = false)

/-- The requests that have a guess. -/
def language : Set (α × ℕ × Bool) := {x | ∃ ℓ, Guess S enc m p G x ℓ}

/-- The census of `S` up to the length `m |enc a|`. -/
noncomputable def census (a : α) : ℕ := (shortMembers S (m.eval (enc a).length)).length

variable {S enc m p G}

/-- **A request with `finalQuery = false` asks whether the census is at least `k`.** -/
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

/-- **At the exact census, a request with `finalQuery = true` asks for the first quantifier.**
If `G` computes `g` whenever its list agrees with `S` on the words of length at most `m |enc a|`,
the request `(a, census, true)` asks whether some `w` of length `p |enc a|` has
`g (a, w) = false`. -/
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

variable (enc m p G) in
/-- The check of a witness `(pairs, witness)` for the request `(a, k, finalQuery)`: the first
components of `pairs` are `k` distinct words of length at most `m |enc a|`, each with an accepted
certificate of the verifier `VS` of `S`, and if `finalQuery`, `witness` has length `p |enc a|` and
`G ((a, witness), ℓ) = false` for the list `ℓ` of the guessed words. -/
def check (VS : List Bool × List Bool → Bool) (pS : Polynomial ℕ) :
    (α × ℕ × Bool) × (List (List Bool × List Bool) × List Bool) → Bool
  | ((a, k, finalQuery), (pairs, witness)) =>
    !((pairs.map Prod.fst).any fun s =>
        decide (1 < (pairs.map Prod.fst).countP fun t => decide (t = s))) &&
      decide ((pairs.map Prod.fst).length = k) &&
      !(pairs.any fun sc => !(decide (sc.1.length ≤ m.eval (enc a).length) &&
        decide (sc.2.length = pS.eval sc.1.length) && VS sc)) &&
      (!finalQuery || (decide (witness.length = p.eval (enc a).length) &&
        !G ((a, witness), pairs.map Prod.fst)))

theorem check_eq_true_iff {VS : List Bool × List Bool → Bool} {pS : Polynomial ℕ} {a : α}
    {k : ℕ} {finalQuery : Bool} {pairs : List (List Bool × List Bool)} {witness : List Bool} :
    check enc m p G VS pS ((a, k, finalQuery), (pairs, witness)) = true ↔
      (pairs.map Prod.fst).Nodup ∧ (pairs.map Prod.fst).length = k ∧
        (∀ sc ∈ pairs, sc.1.length ≤ m.eval (enc a).length ∧
          sc.2.length = pS.eval sc.1.length ∧ VS sc = true) ∧
        (finalQuery = true → witness.length = p.eval (enc a).length ∧
          G ((a, witness), pairs.map Prod.fst) = false) := by
  rw [check, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    List.not_any_one_lt_countP_iff_nodup, and_assoc, and_assoc]
  refine and_congr Iff.rfl (and_congr decide_eq_true_iff (and_congr ?_ ?_))
  · simp [List.any_eq_false, and_assoc]
  · cases finalQuery <;> simp

/-- The witnesses: the certificates of `S` are read by its verifier `VS`. -/
theorem language_eq_setOf_check {VS : List Bool × List Bool → Bool} {pS : Polynomial ℕ}
    (hSV : IsVerifier encBits pS VS S) :
    language S enc m p G = {x | ∃ y, check enc m p G VS pS (x, y) = true} := by
  classical
  ext ⟨a, k, finalQuery⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ℓ, hnd, hlen, hmem, hw⟩
    have hcert (s : List Bool) (hs : s ∈ S) :
        ∃ c, c.length = pS.eval s.length ∧ VS (s, c) = true := (hSV s).1 hs
    let cert : List Bool → List Bool := fun s => if hs : s ∈ S then (hcert s hs).choose else []
    have hmap : (ℓ.map fun s => (s, cert s)).map Prod.fst = ℓ := by
      rw [List.map_map]
      exact List.map_id' ℓ
    refine ⟨(ℓ.map fun s => (s, cert s),
      if h : finalQuery = true then (hw h).choose else []), check_eq_true_iff.mpr
      ⟨by rw [hmap]; exact hnd, by rw [hmap]; exact hlen, fun sc hsc => ?_, fun h => ?_⟩⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsc
      have hsS := (hmem s hs).1
      simp only [cert, hsS, ↓reduceDIte]
      exact ⟨(hmem s hs).2, (hcert s hsS).choose_spec.1, (hcert s hsS).choose_spec.2⟩
    · simp only [h, ↓reduceDIte, hmap]
      exact (hw h).choose_spec
  · rintro ⟨⟨pairs, w⟩, hy⟩
    obtain ⟨hnd, hlen, hpairs, hw⟩ := check_eq_true_iff.mp hy
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
  -- the same function, with its components read by projections
  have h : ComputableInPolyTime
      (fun z : (α × ℕ × Bool) × (List (List Bool × List Bool) × List Bool) =>
        !((z.2.1.map Prod.fst).any fun s =>
            decide (1 < (z.2.1.map Prod.fst).countP fun t => decide (t = s))) &&
          decide ((z.2.1.map Prod.fst).length = z.1.2.1) &&
          !(z.2.1.any fun sc => !(decide (sc.1.length ≤ m.eval (enc z.1.1).length) &&
            decide (sc.2.length = pS.eval sc.1.length) && VS sc)) &&
          (!z.1.2.2 || (decide (z.2.2.length = p.eval (enc z.1.1).length) &&
            !G ((z.1.1, z.2.2), z.2.1.map Prod.fst))))
      (encPair (encPair enc (encPair encUnary encBool))
        (encPair (encList (encPair encBits encBits)) encBits)) encBool := by
    fun_prop
  exact h

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
  obtain ⟨a, k, finalQuery⟩ := x
  obtain ⟨pairs, w⟩ := y
  obtain ⟨hnd, hlen, hpairs, hw⟩ := check_eq_true_iff.mp hy
  set n := (enc a).length
  refine ⟨(pairs, if finalQuery = true then w else []), check_eq_true_iff.mpr
    ⟨hnd, hlen, hpairs, fun h => by simpa only [h, ↓reduceIte] using hw h⟩, ?_⟩
  -- the guessed words are distinct short members of `S`, so there are at most census many
  have hcount : pairs.length ≤ c * (m.eval n + 1) ^ d := by
    have hle := length_le_length_shortMembers (S := S) (n := m.eval n) hnd fun s hs => by
      obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hs
      obtain ⟨hlenS, hc, hV⟩ := hpairs sc hsc
      exact ⟨(hSV sc.1).2 ⟨sc.2, by rw [encBits_apply]; exact hc, hV⟩, hlenS⟩
    rw [List.length_map] at hle
    exact hle.trans (hcensus _)
  have hpair (sc : List Bool × List Bool) (hsc : sc ∈ pairs) :
      2 * (encPair encBits encBits sc).length + 1 ≤
        4 * m.eval n + 2 * pS.eval (m.eval n) + 3 := by
    obtain ⟨hlenS, hc, -⟩ := hpairs sc hsc
    have hpS : pS.eval sc.1.length ≤ pS.eval (m.eval n) := pS.eval_mono hlenS
    enc_len [hc]
  have hlist : (encList (encPair encBits encBits) pairs).length ≤
      c * (m.eval n + 1) ^ d * (4 * m.eval n + 2 * pS.eval (m.eval n) + 3) := by
    rw [length_encList]
    have h := List.sum_le_length_nsmul
      (pairs.map fun sc => 2 * (encPair encBits encBits sc).length + 1)
      (4 * m.eval n + 2 * pS.eval (m.eval n) + 3) fun z hz => by
        obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hz
        exact hpair sc hsc
    rw [List.length_map, smul_eq_mul] at h
    exact h.trans (Nat.mul_le_mul_right _ hcount)
  have hword : (if finalQuery = true then w else []).length ≤ p.eval n := by
    split_ifs with h
    · exact (hw h).1.le
    · exact Nat.zero_le _
  have hn : n ≤ (encPair enc (encPair encUnary encBool) (a, k, finalQuery)).length :=
    length_le_encPair_left enc (encPair encUnary encBool) (a, k, finalQuery)
  refine le_trans ?_ (Polynomial.eval_mono _ hn)
  rw [length_encPair, encBits_apply]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_comp, Polynomial.eval_ofNat]
  omega

/-! ### Binary search with one request per round -/

/-- One round of binary search on the interval `(lo, hi)`: if `lo < hi`, test the midpoint
`mid = ⌈(lo + hi) / 2⌉` with `P` and keep `(mid, hi)` or `(lo, mid - 1)`. -/
def searchStep (P : ℕ → Bool) (st : ℕ × ℕ) : ℕ × ℕ :=
  if st.1 < st.2 then
    if P ((st.1 + st.2 + 1) / 2) then ((st.1 + st.2 + 1) / 2, st.2)
    else (st.1, (st.1 + st.2 + 1) / 2 - 1)
  else st

/-- A round keeps the threshold `C` of `P k = (k ≤ C)` inside the interval and halves it. -/
theorem searchStep_spec {C : ℕ} {st : ℕ × ℕ} (h₁ : st.1 ≤ C) (h₂ : C ≤ st.2) :
    (searchStep (fun k => decide (k ≤ C)) st).1 ≤ C ∧
      C ≤ (searchStep (fun k => decide (k ≤ C)) st).2 ∧
      (searchStep (fun k => decide (k ≤ C)) st).2 - (searchStep (fun k => decide (k ≤ C)) st).1 ≤
        (st.2 - st.1) / 2 := by
  unfold searchStep
  by_cases h : st.1 < st.2
  · by_cases h' : (st.1 + st.2 + 1) / 2 ≤ C
    · simp only [h, h', decide_true, ↓reduceIte]
      refine ⟨trivial, ?_, ?_⟩ <;> omega
    · simp only [h, h', decide_false, ↓reduceIte, Bool.false_eq_true]
      refine ⟨?_, ?_, ?_⟩ <;> omega
  · simp only [h, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-- After `i` rounds from `(0, N)` the interval contains `C` and has length at most `N / 2 ^ i`. -/
theorem iterate_searchStep_spec {C N : ℕ} (hC : C ≤ N) (i : ℕ) :
    ((searchStep (fun k => decide (k ≤ C)))^[i] (0, N)).1 ≤ C ∧
      C ≤ ((searchStep (fun k => decide (k ≤ C)))^[i] (0, N)).2 ∧
      ((searchStep (fun k => decide (k ≤ C)))^[i] (0, N)).2 -
        ((searchStep (fun k => decide (k ≤ C)))^[i] (0, N)).1 ≤ N / 2 ^ i := by
  induction i with
  | zero => exact ⟨Nat.zero_le _, hC, by simp⟩
  | succ i ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    obtain ⟨h₁', h₂', h₃'⟩ := searchStep_spec h₁ h₂
    rw [Function.iterate_succ_apply']
    refine ⟨h₁', h₂', h₃'.trans ?_⟩
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right h₃

/-- **Binary search finds the threshold** after `count` rounds when `N < 2 ^ count`. -/
theorem fst_iterate_searchStep {C N count : ℕ} (hC : C ≤ N) (hcount : N < 2 ^ count) :
    ((searchStep (fun k => decide (k ≤ C)))^[count] (0, N)).1 = C := by
  obtain ⟨h₁, h₂, h₃⟩ := iterate_searchStep_spec hC count
  rw [Nat.div_eq_of_lt hcount] at h₃
  omega

/-- One round against an oracle: the midpoint `k` is tested by one request for `req (a, k)`. -/
def searchStepProgram (req : α × ℕ → List Bool) (a : α) (st : ℕ × ℕ) :
    WordQueryComp Unit (ℕ × ℕ) :=
  if st.1 < st.2 then
    (fun b => if b then ((st.1 + st.2 + 1) / 2, st.2) else (st.1, (st.1 + st.2 + 1) / 2 - 1)) <$>
      queryBit (req (a, (st.1 + st.2 + 1) / 2))
  else pure st

open Classical in
theorem interpret_searchStepProgram (A : Set (List Bool)) (req : α × ℕ → List Bool) (a : α)
    (st : ℕ × ℕ) :
    OracleComp.interpret (m := Id) (languageOracle A) (searchStepProgram req a st) =
      searchStep (fun k => decide (req (a, k) ∈ A)) st := by
  unfold searchStepProgram searchStep
  by_cases h : st.1 < st.2
  · simp only [h, ↓reduceIte, OracleComp.interpret_map, interpret_queryBit]
    rfl
  · simp only [h, ↓reduceIte]
    rfl

/-- A round makes at most one request. -/
theorem length_queriesWith_searchStepProgram_le (answer : Unit × List Bool → List Bool)
    (req : α × ℕ → List Bool) (a : α) (st : ℕ × ℕ) :
    (OracleComp.queriesWith answer (searchStepProgram req a st)).length ≤ 1 := by
  unfold searchStepProgram
  split_ifs <;> simp

/-- The algorithm: `count a` rounds of binary search from `(0, N a)` with the requests `req`,
then one request `fin (a, lo)` at the threshold found. -/
def program (req fin : α × ℕ → List Bool) (N count : α → ℕ) (a : α) : WordQueryComp Unit Bool :=
  OracleComp.iterate (count a) (searchStepProgram req a) (0, N a) >>= fun st =>
    queryBit (fin (a, st.1))

open Classical in
theorem interpret_program (A : Set (List Bool)) (req fin : α × ℕ → List Bool) (N count : α → ℕ)
    (a : α) :
    OracleComp.interpret (m := Id) (languageOracle A) (program req fin N count a) =
      decide (fin (a, ((searchStep fun k => decide (req (a, k) ∈ A))^[count a] (0, N a)).1) ∈
        A) := by
  rw [program, OracleComp.interpret_bind, OracleComp.interpret_id_iterate]
  simp only [interpret_searchStepProgram]
  exact interpret_queryBit A _

/-- The algorithm makes at most `count a + 1` requests. -/
theorem length_queriesWith_program_le (answer : Unit × List Bool → List Bool)
    (req fin : α × ℕ → List Bool) (N count : α → ℕ) (a : α) :
    (OracleComp.queriesWith answer (program req fin N count a)).length ≤ count a + 1 := by
  rw [program, OracleComp.queriesWith_bind, List.length_append, queriesWith_queryBit,
    List.length_singleton]
  exact Nat.add_le_add_right ((OracleComp.length_queriesWith_iterate_le answer
    (length_queriesWith_searchStepProgram_le answer req a) _ _).trans (Nat.mul_one _).le) 1

open Probability in
/-- **The algorithm is strict oracle PPT** when the requests, the bound `N` and the count are
polynomial-time. Every reachable interval lies within `[0, N a]`. -/
theorem isOraclePPTOn_program {enc : α ↪ List Bool} {req fin : α × ℕ → List Bool}
    {N count : α → ℕ} (hreq : ComputableInPolyTime req (encPair enc encUnary) encBits)
    (hfin : ComputableInPolyTime fin (encPair enc encUnary) encBits)
    (hN : ComputableInPolyTime N enc encUnary) (hcount : ComputableInPolyTime count enc encUnary) :
    IsOraclePPTOn enc encBool
      (fun a => OracleComp.interpret ProbOracleComp.query (program req fin N count a)) := by
  have hmid : ComputableInPolyTime (fun pair : α × ℕ × ℕ => (pair.2.1 + pair.2.2 + 1) / 2)
      (encPair enc (encPair encUnary encUnary)) encUnary :=
    (ComputableInPolyTime.unary_div_const 2).comp
      (g := fun pair : α × ℕ × ℕ => pair.2.1 + pair.2.2 + 1) (by fun_prop)
  have hq : IsOraclePPTOn (encPair enc (encPair encUnary encUnary)) encBool
      (fun pair : α × ℕ × ℕ => OracleComp.interpret ProbOracleComp.query
        (queryBit (req (pair.1, (pair.2.1 + pair.2.2 + 1) / 2)))) :=
    isOraclePPTOn_queryBit (input := encPair enc (encPair encUnary encUnary))
      (req := fun pair : α × ℕ × ℕ => req (pair.1, (pair.2.1 + pair.2.2 + 1) / 2))
      (hreq.comp (g := fun pair : α × ℕ × ℕ => (pair.1, (pair.2.1 + pair.2.2 + 1) / 2))
        ((ComputableInPolyTime.fst _ _).prod hmid))
  have hpost : ComputableInPolyTime (fun x : (α × ℕ × ℕ) × Bool =>
      if x.2 then ((x.1.2.1 + x.1.2.2 + 1) / 2, x.1.2.2)
      else (x.1.2.1, (x.1.2.1 + x.1.2.2 + 1) / 2 - 1))
      (encPair (encPair enc (encPair encUnary encUnary)) encBool) (encPair encUnary encUnary) := by
    have hmid' : ComputableInPolyTime (fun x : (α × ℕ × ℕ) × Bool => (x.1.2.1 + x.1.2.2 + 1) / 2)
        (encPair (encPair enc (encPair encUnary encUnary)) encBool) encUnary :=
      hmid.comp (g := fun x : (α × ℕ × ℕ) × Bool => x.1) (.fst _ _)
    have hlo : ComputableInPolyTime (fun x : (α × ℕ × ℕ) × Bool => x.1.2.1)
        (encPair (encPair enc (encPair encUnary encUnary)) encBool) encUnary := by fun_prop
    have hhi : ComputableInPolyTime (fun x : (α × ℕ × ℕ) × Bool => x.1.2.2)
        (encPair (encPair enc (encPair encUnary encUnary)) encBool) encUnary := by fun_prop
    exact ComputableInPolyTime.ite' (ComputableInPolyTime.snd _ _) (hmid'.prod hhi)
      (hlo.prod (ComputableInPolyTime.unary_sub' hmid' (ComputableInPolyTime.const 1)))
  have hyes := hq.map_with' (f := fun pair b => if b then ((pair.2.1 + pair.2.2 + 1) / 2, pair.2.2)
    else (pair.2.1, (pair.2.1 + pair.2.2 + 1) / 2 - 1)) hpost
  have hno : IsOraclePPTOn (Operation := Unit) (encPair enc (encPair encUnary encUnary))
      (encPair encUnary encUnary) (fun pair : α × ℕ × ℕ => pure pair.2) :=
    (ComputableInPolyTime.snd _ _).isOraclePPTOn
  have hcond : ComputableInPolyTime (fun pair : α × ℕ × ℕ => decide (pair.2.1 < pair.2.2))
      (encPair enc (encPair encUnary encUnary)) encBool := by fun_prop
  have hstep : IsOraclePPTOn (encPair enc (encPair encUnary encUnary)) (encPair encUnary encUnary)
      (fun pair : α × ℕ × ℕ => OracleComp.interpret ProbOracleComp.query
        (searchStepProgram req pair.1 pair.2)) := by
    refine (IsOraclePPTOn.ite' (condition := fun pair : α × ℕ × ℕ => pair.2.1 < pair.2.2) hcond
      hyes hno).congr fun pair State oracle s => ?_
    unfold searchStepProgram
    split_ifs <;> simp only [OracleComp.interpret_map, OracleComp.interpret_pure]
  have hinit : ComputableInPolyTime (fun a => ((0 : ℕ), N a)) enc (encPair encUnary encUnary) :=
    (ComputableInPolyTime.const 0).prod hN
  have hsize : PolyBounded (fun a => (enc a).length) (fun a => 3 * N a + 1) :=
    ((PolyBounded.const 3).mul hN.polyBounded).add (.const 1)
  have hit := IsOraclePPTOn.iterateWith_spec' (input := enc)
    (stateEncoding := encPair encUnary encUnary) (count := count)
    (initial := fun a => ((0 : ℕ), N a))
    (step := fun a st => OracleComp.interpret ProbOracleComp.query (searchStepProgram req a st))
    hcount hinit hstep (fun a _ st => st.1 ≤ st.2 ∧ st.2 ≤ N a)
    (fun a => ⟨Nat.zero_le _, le_rfl⟩) (fun a i st _ hinv next hnext => by
      unfold searchStepProgram at hnext
      by_cases h : st.1 < st.2
      · simp only [h, ↓reduceIte, OracleComp.interpret_map] at hnext
        obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      · simp only [h, ↓reduceIte, OracleComp.interpret_pure] at hnext
        rw [OracleComp.eq_of_mem_supportWith_pure hnext]
        exact hinv)
    hsize (fun a i st _ hinv => by enc_len)
  have hfinal : IsOraclePPTOn (encPair enc (encPair encUnary encUnary)) encBool
      (fun pair : α × ℕ × ℕ => OracleComp.interpret ProbOracleComp.query
        (queryBit (fin (pair.1, pair.2.1)))) :=
    isOraclePPTOn_queryBit (input := encPair enc (encPair encUnary encUnary))
      (req := fun pair : α × ℕ × ℕ => fin (pair.1, pair.2.1))
      (hfin.comp (g := fun pair : α × ℕ × ℕ => (pair.1, pair.2.1))
        ((ComputableInPolyTime.fst _ _).prod (ComputableInPolyTime.snd _ _).fst'))
  have hbind := hit.1.bind_with (second := fun a st => OracleComp.interpret ProbOracleComp.query
    (queryBit (fin (a, st.1)))) hfinal
  simpa only [program, OracleComp.interpret_bind, OracleComp.interpret_iterate] using hbind

end KadinCensus


/-! ### Kadin's theorem -/

open Classical in
/-- **`Σ₂ ⊆ P^{NP[O(log n)]}` under a sparse Turing-complete set for `NP`.** Binary search with
requests to `SAT` finds the census of `S` up to the length of the oracle words, and one more
request, at the exact census, guesses the short members of `S` together with the first certificate
of the `Σ₂` problem [Hemaspaandra and Ogihara, Theorem 1.14][HemaspaandraOgihara2002]. -/
theorem SigmaP_two_subset_PNPLog_of_sparse (hsparse : S ∈ SPARSE encBits) (hS : S ∈ NP encBits)
    (hSAT : SAT ∈ PWithOracle S encCNF) (enc : α ↪ List Bool) :
    SigmaP 2 enc ⊆ PNPLog enc := by
  intro L hL
  -- `a ∈ L ↔ ∃ w, (a, w) ∈ B` with `B ∈ coNP`, and `Bᶜ ∈ NP ⊆ P^S`
  obtain ⟨p, B, hB, hLB⟩ := exists_mem_PiP_of_mem_SigmaP_succ (k := 1) hL
  rw [PiP_one_eq_coNP] at hB
  obtain ⟨g, hg, hgB⟩ := (CookLevin.SAT_npHard _ _ hB).mem_PWithOracle hSAT
  obtain ⟨G, q, hG, hGg⟩ := hg.exists_listOracle_bool
  -- the oracle words asked on `(a, w)` with `|w| = p |enc a|` have length at most `m |enc a|`
  let m : Polynomial ℕ := q.comp (2 * Polynomial.X + 1 + p)
  have hD := KadinCensus.language_mem_NP (m := m) (p := p) hS hsparse hG
  obtain ⟨red, hred, hDred⟩ := CookLevin.SAT_npHard _ _ hD
  have henc : ComputableInPolyTime (fun φ : Cslib.Logic.PL.CNF ℕ => encCNF φ) encCNF encBits :=
    .of_eq fun _ => rfl
  have hreqb (b : Bool) : ComputableInPolyTime (fun x : α × ℕ => encCNF (red (x.1, x.2, b)))
      (encPair enc encUnary) encBits :=
    henc.comp (hred.comp (g := fun x : α × ℕ => (x.1, x.2, b))
      ((ComputableInPolyTime.fst _ _).prod ((ComputableInPolyTime.snd _ _).prod
        (ComputableInPolyTime.const b))))
  have hmemA (x : α × ℕ × Bool) :
      encCNF (red x) ∈ encCNF '' SAT ↔ x ∈ KadinCensus.language S enc m p G := by
    rw [hDred x]
    exact ⟨fun ⟨_, h, he⟩ => encCNF.injective he ▸ h, fun h => ⟨_, h, rfl⟩⟩
  -- the census bound and the number of rounds
  obtain ⟨c, d, hcensus⟩ := exists_length_shortMembers_le hsparse
  let N : α → ℕ := fun a => c * (m.eval (enc a).length + 1) ^ d
  let count : α → ℕ := fun a => Nat.clog 2 (N a + 1)
  have hN : ComputableInPolyTime N enc encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (m + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length enc)).of_enc_eq fun a => by simp [N]
  have hcount : ComputableInPolyTime count enc encUnary :=
    (ComputableInPolyTime.unary_clog_const 2).comp
      (ComputableInPolyTime.unary_add' hN (ComputableInPolyTime.const 1))
  obtain ⟨K, hK⟩ := PolynomiallyBounded.exists_clog_le_mul_log
    (s := fun n => c * (m.eval n + 1) ^ d + 1) (by fun_prop)
  let prog := KadinCensus.program (fun x => encCNF (red (x.1, x.2, false)))
    (fun x => encCNF (red (x.1, x.2, true))) N count
  refine mem_PNPLog_of_mem_PWithOracleQueries (c := K + 1) image_SAT_mem_NP
    ⟨fun a => OracleComp.interpret (m := Id) (languageOracle (encCNF '' SAT)) (prog a),
      ⟨prog, KadinCensus.isOraclePPTOn_program (hreqb false) (hreqb true) hN hcount,
        fun a => ⟨rfl, ?_⟩⟩, fun a => ?_⟩
  · refine (KadinCensus.length_queriesWith_program_le _ _ _ _ _ a).trans ?_
    have := hK (enc a).length
    simp only [N, count] at this ⊢
    nlinarith [Nat.zero_le (Nat.log 2 (enc a).length)]
  -- correctness: binary search finds the census, and the last request decides `L`
  have hP : (fun k => decide (encCNF (red (a, k, false)) ∈ encCNF '' SAT)) =
      fun k => decide (k ≤ KadinCensus.census S enc m a) := by
    funext k
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hmemA,
      KadinCensus.mem_language_false_iff]
  have hcen : KadinCensus.census S enc m a ≤ N a := hcensus _
  have hlt : N a < 2 ^ count a := Nat.lt_of_succ_le (Nat.le_pow_clog (by norm_num) _)
  have hlast := KadinCensus.mem_language_census_true_iff (S := S) (enc := enc) (m := m) (p := p)
    (G := G) (a := a) (g := g) fun w ℓ hw hℓ => hGg (a, w) ℓ fun s hs =>
      hℓ s (by simpa [m, length_encPair, hw] using hs)
  change a ∈ L ↔ OracleComp.interpret (m := Id) (languageOracle (encCNF '' SAT))
    (KadinCensus.program (fun x => encCNF (red (x.1, x.2, false)))
      (fun x => encCNF (red (x.1, x.2, true))) N count a) = true
  rw [KadinCensus.interpret_program, decide_eq_true_iff]
  dsimp only
  rw [hmemA, hP, KadinCensus.fst_iterate_searchStep hcen hlt, hlast, hLB a]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  rw [← Bool.not_eq_true, ← hgB, Set.mem_compl_iff, not_not]

/-- **Kadin's theorem** [Kadin][Kadin1989] [Hemaspaandra and Ogihara, Theorem 1.14]
[HemaspaandraOgihara2002]: if `NP` has a sparse polynomial-time Turing-complete set, that is a
sparse `S ∈ NP` with `SAT` decided in polynomial time relative to `S`, then the polynomial
hierarchy is contained in `P^{NP[O(log n)]}`. -/
theorem PH_subset_PNPLog_of_sparse (hsparse : S ∈ SPARSE encBits) (hS : S ∈ NP encBits)
    (hSAT : SAT ∈ PWithOracle S encCNF) (enc : α ↪ List Bool) :
    PH enc ⊆ PNPLog enc := by
  rw [PH_eq_SigmaP_two_of_SAT_mem_PWithOracle hsparse hSAT enc]
  exact SigmaP_two_subset_PNPLog_of_sparse hsparse hS hSAT enc

end Cslib.Complexity
