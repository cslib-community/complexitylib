/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Cslib.Foundations.Data.Polynomial.Monotone
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Proof systems

A *proof system* for a set `L` in the sense of [Cook and Reckhow][CookReckhow1979] is a function,
computable in polynomial time, from words onto `L` (`Cslib.Complexity.ProofSystem`). A word `π` is
a proof of `P π`: every word proves a member of `L`, and every member of `L` has a proof. A proof
system is *polynomially bounded* when every member has a proof of length polynomial in its own
length (`Cslib.Complexity.ProofSystem.PolynomiallyBounded`).

Proof systems are compared by simulation: `Q` *simulates* `P` when every proof for `P` can be
replaced by a proof for `Q` of the same member that is at most polynomially longer, and `Q`
*p-simulates* `P` when the replacement is computed in polynomial time. Simulation transfers
polynomial bounds (`Cslib.Complexity.ProofSystem.PolynomiallyBounded.of_simulates`).

A set with a polynomially bounded proof system is in `NP`, since a short proof is a certificate
checked by computing the member it proves. Conversely, a nonempty set in `NP` whose encoding has a
decoder has a polynomially bounded proof system: a proof is an encoded instance followed by a
certificate the verifier accepts, and a proof the verifier rejects proves a fixed member
(`Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_mem_NP`). Applied to a
`coNP`-complete set, this is the theorem of Cook and Reckhow: `coNP ⊆ NP` exactly when that set has
a polynomially bounded proof system. For the unsatisfiable formulas in conjunctive normal form,
which are `coNP`-complete by the Cook–Levin theorem, this reads: `NP = coNP` exactly when some
propositional refutation system is polynomially bounded
(`Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded`).

Proofs are words over `Bool`, as in [CookReckhow1979]. The verifier construction uses a total
decoder: even a malformed word can decode to an instance with an accepted certificate. It proves
that instance when the verifier and certificate-length checks pass, and a fixed member otherwise.

## Main definitions

* `Cslib.Complexity.ProofSystem`: Cook–Reckhow proof systems.
* `Cslib.Complexity.ProofSystem.PolynomiallyBounded`: polynomially bounded proof systems.
* `Cslib.Complexity.ProofSystem.Simulates`, `Cslib.Complexity.ProofSystem.PSimulates`:
  simulation and p-simulation.
* `Cslib.Complexity.ProofSystem.ofVerifier`: the proof system of a verifier.

## Main results

* `Cslib.Complexity.ProofSystem.PSimulates.simulates`: p-simulation implies simulation; both are
  preorders.
* `Cslib.Complexity.ProofSystem.PolynomiallyBounded.of_simulates`: a proof system simulating a
  polynomially bounded one is polynomially bounded.
* `Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_mem_NP`: a nonempty set with a
  decodable encoding has a polynomially bounded proof system exactly when it is in `NP`.
* `Cslib.Complexity.ProofSystem.coNP_subset_NP_iff_exists_polynomiallyBounded`: `coNP ⊆ NP`
  exactly when a `coNP`-complete set has a polynomially bounded proof system.
* `Cslib.Complexity.ProofSystem.NP_eq_coNP_iff_exists_polynomiallyBounded`: `NP = coNP` exactly
  when `UNSAT` has a polynomially bounded proof system [CookReckhow1979].

## References

* [S. A. Cook, R. A. Reckhow, *The relative efficiency of propositional proof
  systems*][CookReckhow1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} {L : Set α}

/-- A **proof system** for `L` [CookReckhow1979]: a function, computable in polynomial time, from
words onto `L`. A word `π` is a proof of `P π`; every word proves a member of `L`, and every member
of `L` has a proof. -/
structure ProofSystem (enc : α ↪ List Bool) (L : Set α) where
  /-- The member of `L` that a word proves. -/
  toFun : List Bool → α
  /-- The member a proof proves is computed in polynomial time. -/
  computable : ComputableInPolyTime toFun encBits enc
  /-- The proved members are exactly the members of `L`. -/
  range_eq : Set.range toFun = L

namespace ProofSystem

instance : CoeFun (ProofSystem enc L) fun _ => List Bool → α := ⟨toFun⟩

/-- **Soundness**: every word proves a member of `L`. -/
theorem mem (P : ProofSystem enc L) (π : List Bool) : P π ∈ L :=
  P.range_eq.subset ⟨π, rfl⟩

/-- **Completeness**: every member of `L` has a proof. -/
theorem exists_eq (P : ProofSystem enc L) {a : α} (ha : a ∈ L) : ∃ π, P π = a :=
  P.range_eq.symm.subset ha

/-- A set with a proof system is nonempty. -/
theorem nonempty (P : ProofSystem enc L) : L.Nonempty := ⟨P [], P.mem []⟩

/-! ### Polynomial bounds and simulations -/

/-- `P` is **polynomially bounded** [CookReckhow1979]: for a polynomial `p`, every member `a` of
`L` has a proof of length at most `p (enc a).length`. -/
def PolynomiallyBounded (P : ProofSystem enc L) : Prop :=
  ∃ p : Polynomial ℕ, ∀ a ∈ L, ∃ π, P π = a ∧ π.length ≤ p.eval (enc a).length

/-- `Q` **simulates** `P`: for a polynomial `p`, every proof `π` for `P` can be replaced by a proof
for `Q` of the same member, of length at most `p π.length`. -/
def Simulates (Q P : ProofSystem enc L) : Prop :=
  ∃ p : Polynomial ℕ, ∀ π, ∃ π', Q π' = P π ∧ π'.length ≤ p.eval π.length

/-- `Q` **p-simulates** `P` [CookReckhow1979]: a function computable in polynomial time translates
every proof for `P` into a proof for `Q` of the same member. -/
def PSimulates (Q P : ProofSystem enc L) : Prop :=
  ∃ t : List Bool → List Bool, ComputableInPolyTime t encBits encBits ∧ ∀ π, Q (t π) = P π

namespace Simulates

variable {P Q R : ProofSystem enc L}

/-- Every proof system simulates itself. -/
@[refl]
theorem refl : P.Simulates P := ⟨.X, fun π => ⟨π, rfl, by simp⟩⟩

/-- Simulation is transitive. -/
@[trans]
theorem trans (hRQ : R.Simulates Q) (hQP : Q.Simulates P) : R.Simulates P := by
  obtain ⟨q, hq⟩ := hRQ
  obtain ⟨p, hp⟩ := hQP
  refine ⟨q.comp p, fun π => ?_⟩
  obtain ⟨π', hπ', hlen'⟩ := hp π
  obtain ⟨π'', hπ'', hlen''⟩ := hq π'
  exact ⟨π'', hπ''.trans hπ', by
    rw [Polynomial.eval_comp]
    exact hlen''.trans (q.eval_mono hlen')⟩

end Simulates

namespace PSimulates

variable {P Q R : ProofSystem enc L}

/-- Every proof system p-simulates itself. -/
@[refl]
theorem refl : P.PSimulates P := ⟨id, .id', fun _ => rfl⟩

/-- p-simulation is transitive. -/
@[trans]
theorem trans (hRQ : R.PSimulates Q) (hQP : Q.PSimulates P) : R.PSimulates P := by
  obtain ⟨t, ht, hRQ⟩ := hRQ
  obtain ⟨u, hu, hQP⟩ := hQP
  exact ⟨t ∘ u, ht.comp hu, fun π => (hRQ (u π)).trans (hQP π)⟩

/-- **p-simulation implies simulation**: a translation computed in polynomial time produces proofs
of polynomial length. -/
theorem simulates (h : Q.PSimulates P) : Q.Simulates P := by
  obtain ⟨t, ht, htQP⟩ := h
  obtain ⟨c, d, hle⟩ := ht.polyBounded_length.exists_le
  exact ⟨.C c * (.X + 1) ^ d, fun π => ⟨t π, htQP π, by simpa using hle π⟩⟩

end PSimulates

/-- **Simulation transfers polynomial bounds**: a proof system simulating a polynomially bounded
proof system is polynomially bounded. -/
theorem PolynomiallyBounded.of_simulates {P Q : ProofSystem enc L} (hP : P.PolynomiallyBounded)
    (hQP : Q.Simulates P) : Q.PolynomiallyBounded := by
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQP
  refine ⟨q.comp p, fun a ha => ?_⟩
  obtain ⟨π, rfl, hlen⟩ := hp a ha
  obtain ⟨π', hπ', hlen'⟩ := hq π
  exact ⟨π', hπ', by
    rw [Polynomial.eval_comp]
    exact hlen'.trans (q.eval_mono hlen)⟩

/-! ### Polynomially bounded proof systems and `NP` -/

/-- **A set with a polynomially bounded proof system is in `NP`**: a short proof is a certificate,
checked by computing the member it proves. -/
theorem PolynomiallyBounded.mem_NP {P : ProofSystem enc L} (hP : P.PolynomiallyBounded) :
    L ∈ NP enc := by
  classical
  obtain ⟨p, hp⟩ := hP
  have hcheck : ComputableInPolyTime (fun x : α × List Bool => decide (P x.2 = x.1))
      (encPair enc encBits) encBool :=
    decide_eq' (P.computable.comp (snd enc encBits)) (fst enc encBits)
  have h := mem_NP_of_witness (p := p) Decoder.bits hcheck (R := fun a π => P π = a)
    (fun _ _ => decide_eq_true_iff) fun a π hπ => hp a (hπ ▸ P.mem π)
  have hL : {a | ∃ π, P π = a} = L := P.range_eq
  rwa [hL] at h

section OfVerifier

variable {p : Polynomial ℕ} {V : α × List Bool → Bool}

/-- The instance a word presents to a verifier: the decoding of its first frame. -/
def verifierInstance (D : Decoder enc) (π : List Bool) : α := D.decode (unframe π)

/-- Whether the verifier `V` accepts a word as an instance followed by a certificate of the
prescribed length `p`. -/
def verifierAccepts (D : Decoder enc) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (π : List Bool) : Bool :=
  V (verifierInstance D π, dropFrame π) &&
    decide ((dropFrame π).length = p.eval (enc (verifierInstance D π)).length)

/-- The **proof system of a verifier** `V` for `L`, with a default member `a₀`. Each word is
decoded into an instance and a certificate using the total decoder `D`, `unframe` and `dropFrame`.
It proves the decoded instance if `V` accepts and the certificate has the prescribed length;
otherwise it proves `a₀`. A malformed frame can pass these checks. -/
def ofVerifier (D : Decoder enc) (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hVL : IsVerifier enc p V L) {a₀ : α} (ha₀ : a₀ ∈ L) : ProofSystem enc L where
  toFun π := if verifierAccepts D p V π then verifierInstance D π else a₀
  computable := by
    obtain ⟨_, _, hD⟩ := D.computable
    have hi : ComputableInPolyTime (verifierInstance D) encBits enc :=
      hD.computableInPolyTime.comp unframe
    have hlen : ComputableInPolyTime
        (fun π => p.eval (enc (verifierInstance D π)).length) encBits encUnary :=
      (unary_eval p).comp ((encoding_length enc).comp hi)
    have hacc : ComputableInPolyTime (verifierAccepts D p V) encBits encBool :=
      bool_and' (hV.comp (hi.prod dropFrame))
        (decide_eq' (length_bits.comp dropFrame) hlen)
    exact hacc.ite' hi (const a₀)
  range_eq := by
    refine Set.Subset.antisymm ?_ fun a ha => ?_
    · rintro _ ⟨π, rfl⟩
      dsimp only
      split_ifs with h
      · simp only [verifierAccepts, Bool.and_eq_true, decide_eq_true_eq] at h
        exact (hVL _).2 ⟨_, h.2, h.1⟩
      · exact ha₀
    · obtain ⟨w, hw, hVw⟩ := (hVL a).1 ha
      refine ⟨frame (enc a) ++ w, ?_⟩
      have hi : verifierInstance D (frame (enc a) ++ w) = a := by
        rw [verifierInstance, unframe_frame_append, D.decode_enc]
      have hacc : verifierAccepts D p V (frame (enc a) ++ w) = true := by
        simp only [verifierAccepts, hi, dropFrame_frame_append, hVw, hw, decide_true,
          Bool.and_self]
      simp only [hacc, ↓reduceIte, hi]

/-- A framed encoded instance followed by an accepted certificate of the prescribed length proves
that instance. -/
theorem ofVerifier_frame_append (D : Decoder enc)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hVL : IsVerifier enc p V L) {a₀ : α} (ha₀ : a₀ ∈ L) {a : α} {w : List Bool}
    (hw : w.length = p.eval (enc a).length) (hVw : V (a, w) = true) :
    ofVerifier D hV hVL ha₀ (frame (enc a) ++ w) = a := by
  have hi : verifierInstance D (frame (enc a) ++ w) = a := by
    rw [verifierInstance, unframe_frame_append, D.decode_enc]
  have hacc : verifierAccepts D p V (frame (enc a) ++ w) = true := by
    simp only [verifierAccepts, hi, dropFrame_frame_append, hVw, hw, decide_true, Bool.and_self]
  change (if verifierAccepts D p V _ then _ else _) = a
  simp only [hacc, ↓reduceIte, hi]

/-- The proof system of a verifier is polynomially bounded: an instance `a` has a proof of length
`2 * (enc a).length + 1 + p (enc a).length`. -/
theorem polynomiallyBounded_ofVerifier (D : Decoder enc)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hVL : IsVerifier enc p V L) {a₀ : α} (ha₀ : a₀ ∈ L) :
    (ofVerifier D hV hVL ha₀).PolynomiallyBounded := by
  refine ⟨2 * .X + 1 + p, fun a ha => ?_⟩
  obtain ⟨w, hw, hVw⟩ := (hVL a).1 ha
  exact ⟨_, ofVerifier_frame_append D hV hVL ha₀ hw hVw, by simp [length_frame, hw]⟩

end OfVerifier

/-- **A set is in `NP` exactly when it has a polynomially bounded proof system**
[CookReckhow1979], for nonempty sets whose encoding has a decoder. -/
theorem exists_polynomiallyBounded_iff_mem_NP (D : Decoder enc) (hL : L.Nonempty) :
    (∃ P : ProofSystem enc L, P.PolynomiallyBounded) ↔ L ∈ NP enc := by
  refine ⟨fun ⟨_, hP⟩ => hP.mem_NP, fun ⟨p, V, hV, hVL⟩ => ?_⟩
  obtain ⟨a₀, ha₀⟩ := hL
  exact ⟨_, polynomiallyBounded_ofVerifier D hV hVL ha₀⟩

/-! ### The theorem of Cook and Reckhow -/

/-- **Cook and Reckhow, for `coNP`-complete sets** [CookReckhow1979]: `coNP ⊆ NP`, for problems
with every encoding of their instances, exactly when a nonempty `coNP`-complete set with a
decodable encoding has a polynomially bounded proof system. -/
theorem coNP_subset_NP_iff_exists_polynomiallyBounded {β : Type} {encB : β ↪ List Bool}
    {B : Set β} (hB : coNPComplete encB B) (D : Decoder encB) (hne : B.Nonempty) :
    (∀ {γ : Type} (encC : γ ↪ List Bool), coNP encC ⊆ NP encC) ↔
      ∃ P : ProofSystem encB B, P.PolynomiallyBounded := by
  rw [exists_polynomiallyBounded_iff_mem_NP D hne]
  exact ⟨fun h => h encB hB.1, fun h _ encC _ hA => (hB.2 encC _ hA).mem_NP h⟩

/-- **The theorem of Cook and Reckhow** [CookReckhow1979], for refutations: `NP = coNP`, for
problems with every encoding of their instances, exactly when some proof system for the
unsatisfiable formulas in conjunctive normal form is polynomially bounded. -/
theorem NP_eq_coNP_iff_exists_polynomiallyBounded :
    (∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) ↔
      ∃ P : ProofSystem encCNF UNSAT, P.PolynomiallyBounded := by
  rw [NP_eq_coNP_iff_coNP_subset_NP]
  exact coNP_subset_NP_iff_exists_polynomiallyBounded CookLevin.UNSAT_coNPComplete cnfDecoder
    ⟨[[]], fun ⟨_, h⟩ => by simp at h⟩

end ProofSystem

end Cslib.Complexity
