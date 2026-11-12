/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import Cslib.Crypto.Protocols.SecretSharing.Shamir
public import CslibFrontier.Crypto.Protocols.PIR.Basic
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product

/-!
# Coalition-private information retrieval and polynomial schemes

[Chor, Goldreich, Kushilevitz and Sudan, Section 2.2][ChorGoldreichKushilevitzSudan1998] extends
one-round private information retrieval from single curious servers to coalitions of up to `t`
colluding servers: for every coalition of at most `t` servers, the joint distribution of the
queries sent to those servers does not depend on the target index `i`.

* **Coalition privacy (`Scheme.IsTPrivate`).** `P.coalitionQuery T i` projects the joint query draw
  onto `T : Finset S`, and `P.IsTPrivate t` asks its law to be independent of `i` whenever
  `T.card ≤ t`. At `t = 0` this holds trivially (`Scheme.isTPrivate_zero`), at `t = 1` it is
  equivalent to single-server `Scheme.IsPrivate` (`Scheme.isTPrivate_one_iff`), and for every `t`
  it is equivalent to the paper's `t`-tuple formulation (`Scheme.isTPrivate_iff_tuple`).
  Both `Scheme.rows` and `Scheme.comap` preserve `IsTPrivate`.
* **Necessity of `t < k` (`Scheme.card_le_communication_of_card_le`).** Generalizing the
  single-server injectivity argument of [CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998],
  when all servers can collude (`|S| ≤ t`), the entire query tuple has an index-independent law, so
  some joint query vector makes the combined answer map injective on the database
  (`2 ^ |ι| ≤ |A| ^ |S|`) and forces at least `|ι|` bits of communication (with no correct
  zero-server scheme on nonempty databases).
* **Shamir linear and degree-`d` hypercube schemes (`PIR.shamir`, `PIR.shamirCube`).** Sharing the
  point indicator `eᵢ` across servers `S` with degree-`t` Shamir secret sharing [Shamir1979] over a
  finite field `F` (`params : Shamir.Params F S`, so `|F| > |S|`) gives a `t`-private scheme
  (`PIR.isTPrivate_shamir`) whose `(t + 1)`-server coalitions can reconstruct `i`
  (`PIR.not_isTPrivate_succ_shamir`). Combining `PIR.shamir` with the matrix `rows` transformation
  gives `(t + 1)`-server `t`-private PIR with `2 (t + 1) m ⌈log₂ |F|⌉` bits for `n ≤ m ^ 2`
  (`PIR.hasTPrivateScheme_of_le_mul_self`). On a `d`-dimensional cube `D → ι`, sharing the `d`
  coordinate indicators and multiplying degree-`t` shares at each server gives a degree-`≤ d t`
  polynomial whose constant term is `x i`: whenever `d t < |S|`, Lagrange interpolation at zero
  recovers `x i` from one field element per server (`PIR.isCorrect_shamirCube`), achieving
  `|S| ((d ℓ + 1) ⌈log₂ |F|⌉)` bits for `n ≤ ℓ ^ d` (`PIR.hasTPrivateScheme_of_le_pow`, with
  `d t + 1` servers). Applying the balancing `rows (Fin ℓ)` transformation of
  [CGKS, Section 3.4, p. 11][ChorGoldreichKushilevitzSudan1998] to `PIR.shamirCube` yields
  `|S| ((d + 1) ℓ ⌈log₂ |F|⌉)` bits for `n ≤ ℓ ^ (d + 1)` whenever `d t < |S|`
  (`PIR.hasTPrivateScheme_rows_of_le_pow`, `PIR.hasTPrivateScheme_prime_rows_of_le_pow`): setting
  `d = c - 1` for `c ≥ 2` and `t ≥ 1` satisfies `(c - 1) t < c t` and instantiates the exact
  `c · t`-server `O(c · t · n ^ (1 / c) · log |F|)` polynomial family noted in
  [CGKS, Section 1.1][ChorGoldreichKushilevitzSudan1998].

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Scheme.coalitionQuery`,
  `Cslib.Crypto.Protocols.PIR.Scheme.tupleQuery`: joint query marginals on server subsets and
  tuples.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate`: perfect information-theoretic `t`-privacy.
* `Cslib.Crypto.Protocols.PIR.HasTPrivateScheme`: existence of a correct, `t`-private `k`-server
  scheme within a bit budget.
* `Cslib.Crypto.Protocols.PIR.shamir`: linear Shamir `t`-private PIR over a finite field.
* `Cslib.Crypto.Protocols.PIR.shamirCube`: degree-`d` polynomial `t`-private PIR on `D → ι`.
* `Cslib.Crypto.Protocols.PIR.zmodShamirParams`: canonical Shamir parameters on `Fin k` over
  `ZMod p` for primes `p > k`.

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.isTPrivate_one_iff`,
  `Cslib.Crypto.Protocols.PIR.Scheme.isTPrivate_iff_tuple`: equivalence with `IsPrivate` at `t = 1`
  and with `t`-tuple query independence.
* `Cslib.Crypto.Protocols.PIR.Scheme.card_le_communication_of_card_le`: full-coalition `t ≥ |S|`
  requires at least `|ι|` bits of communication.
* `Cslib.Crypto.Protocols.PIR.isCorrect_shamir`,
  `Cslib.Crypto.Protocols.PIR.isTPrivate_shamir`,
  `Cslib.Crypto.Protocols.PIR.not_isTPrivate_succ_shamir`: correctness, `t`-privacy, and sharpness
  at threshold `t + 1` of linear Shamir PIR.
* `Cslib.Crypto.Protocols.PIR.isCorrect_shamirCube`,
  `Cslib.Crypto.Protocols.PIR.isTPrivate_shamirCube`,
  `Cslib.Crypto.Protocols.PIR.not_isTPrivate_succ_shamirCube`: correctness (when `|D| * t < |S|`),
  `t`-privacy, and sharpness at threshold `t + 1` of degree-`d` polynomial PIR.
* `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_of_le_mul_self`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_of_le_pow`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_rows_of_le_pow`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_prime_of_le_pow`,
  `Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_prime_rows_of_le_pow`: `(t + 1)`-server `O(√n)`,
  unbalanced `(d t + 1)`-server `O(n ^ (1 / d))`, and balanced `c t`-server `O(n ^ (1 / c))`
  `t`-private schemes for `n`-bit databases.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Sections 1.1, 2.2, 3.4 and 5.1; numbering of the
  authors' journal version of April 21, 1998
* [A. Shamir, *How to Share a Secret*][Shamir1979]
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability Cslib.Crypto.Protocols.SecretSharing

namespace Scheme

variable {ι S R Q A : Type}

section CoalitionDefs

variable (P : Scheme ι S R Q A)

/-- The joint query marginal seen by a coalition `T : Finset S` when the user queries `i`. -/
def coalitionQuery (T : Finset S) (i : ι) : ProbComp (T → Q) :=
  (fun (_, q) (s : T) => q s) <$> P.query i

/-- The joint query marginal seen by an indexed tuple `servers : τ → S` of servers
[CGKS, Section 2.2][ChorGoldreichKushilevitzSudan1998]. -/
def tupleQuery {τ : Type} (servers : τ → S) (i : ι) : ProbComp (τ → Q) :=
  (fun (_, q) j => q (servers j)) <$> P.query i

/-- Perfect `t`-privacy [CGKS, Section 2.2][ChorGoldreichKushilevitzSudan1998]: every coalition of
at most `t` servers sees the same joint query distribution regardless of the target index. -/
def IsTPrivate (t : ℕ) : Prop :=
  ∀ T : Finset S, T.card ≤ t → ∀ i i',
    ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i')

theorem coalitionQuery_eq (T : Finset S) (i : ι) :
    P.coalitionQuery T i = (fun (_, q) (s : T) => q s) <$> P.query i := by
  rw [coalitionQuery]

theorem eval_coalitionQuery (T : Finset S) (i : ι) :
    ProbComp.eval (P.coalitionQuery T i) =
      (ProbComp.eval (P.query i)).map (fun (_, q) (s : T) => q s) := by
  rw [coalitionQuery, ProbComp.eval_map]

theorem eval_tupleQuery {τ : Type} (servers : τ → S) (i : ι) :
    ProbComp.eval (P.tupleQuery servers i) =
      (ProbComp.eval (P.query i)).map (fun (_, q) j => q (servers j)) := by
  rw [tupleQuery, ProbComp.eval_map]

theorem isTPrivate_iff (t : ℕ) :
    P.IsTPrivate t ↔ ∀ T : Finset S, T.card ≤ t → ∀ i i',
      ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i') := by
  rw [IsTPrivate]

/-- Every scheme is `0`-private: the empty coalition sees the unique empty tuple. -/
theorem isTPrivate_zero : P.IsTPrivate 0 := by
  intro T hT i i'
  have hEmpty : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hT)
  subst hEmpty
  ext f
  have hf : ∀ g : (∅ : Finset S) → Q, g = f :=
    fun g => funext fun s => (Finset.notMem_empty s.1 s.2).elim
  have h1 := (ProbComp.eval (P.coalitionQuery ∅ i)).tsum_coe
  have h2 := (ProbComp.eval (P.coalitionQuery ∅ i')).tsum_coe
  rw [tsum_eq_single f fun g hg => (hg (hf g)).elim] at h1 h2
  exact h1.trans h2.symm

end CoalitionDefs

variable {P : Scheme ι S R Q A}

theorem IsTPrivate.eval_coalitionQuery_eq {t : ℕ} (h : P.IsTPrivate t) (T : Finset S)
    (hT : T.card ≤ t) (i i' : ι) :
    ProbComp.eval (P.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T i') :=
  h T hT i i'

theorem IsTPrivate.mono {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂) (h : P.IsTPrivate t₂) : P.IsTPrivate t₁ :=
  fun T hT => h T (hT.trans hle)

/-- `1`-privacy is exactly single-server `IsPrivate`. -/
theorem isTPrivate_one_iff : P.IsTPrivate 1 ↔ P.IsPrivate := by
  rw [P.isPrivate_iff]
  constructor
  · intro h s i i'
    have hsing := h {s} (by simp) i i'
    have hproj (idx : ι) :
        ProbComp.eval (P.serverQuery s idx) =
          (ProbComp.eval (P.coalitionQuery {s} idx)).map
            (fun f => f ⟨s, Finset.mem_singleton_self s⟩) := by
      rw [P.eval_serverQuery, P.eval_coalitionQuery, PMF.map_comp]
      rfl
    rw [hproj i, hproj i', hsing]
  · intro h T hT i i'
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with h0 | h1
    · exact P.isTPrivate_zero T (by omega) i i'
    · obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp h1
      have hlift (idx : ι) :
          ProbComp.eval (P.coalitionQuery {s} idx) =
            (ProbComp.eval (P.serverQuery s idx)).map (fun q _ => q) := by
        rw [P.eval_coalitionQuery, P.eval_serverQuery, PMF.map_comp]
        congr 1
        funext ⟨r, q⟩ ⟨u, hu⟩
        simpa using congrArg q (Finset.mem_singleton.mp hu)
      rw [hlift i, hlift i', h s i i']

theorem IsTPrivate.isPrivate {t : ℕ} (ht : 1 ≤ t) (h : P.IsTPrivate t) : P.IsPrivate :=
  isTPrivate_one_iff.mp (h.mono ht)

/-- A `t`-private scheme hides `i` from any tuple of at most `t` (possibly repeated) servers. -/
theorem IsTPrivate.eval_tupleQuery_eq {τ : Type} [Fintype τ] {t : ℕ}
    (h : P.IsTPrivate t) (servers : τ → S) (hcard : Fintype.card τ ≤ t) (i i' : ι) :
    ProbComp.eval (P.tupleQuery servers i) = ProbComp.eval (P.tupleQuery servers i') := by
  classical
  let T : Finset S := Finset.univ.image servers
  have hT : T.card ≤ t := Finset.card_image_le.trans (by simpa using hcard)
  have hfactor (idx : ι) :
      ProbComp.eval (P.tupleQuery servers idx) =
        (ProbComp.eval (P.coalitionQuery T idx)).map
          (fun f j => f ⟨servers j, Finset.mem_image_of_mem servers (Finset.mem_univ j)⟩) := by
    rw [P.eval_tupleQuery, P.eval_coalitionQuery, PMF.map_comp]
    rfl
  rw [hfactor i, hfactor i', h T hT i i']

/-- `Finset`-based `t`-privacy is equivalent to the `t`-tuple definition of
[CGKS, Section 2.2][ChorGoldreichKushilevitzSudan1998]. -/
theorem isTPrivate_iff_tuple {t : ℕ} :
    P.IsTPrivate t ↔
      ∀ (servers : Fin t → S) (i i' : ι),
        ProbComp.eval (P.tupleQuery servers i) = ProbComp.eval (P.tupleQuery servers i') := by
  constructor
  · intro h servers i i'
    exact h.eval_tupleQuery_eq servers (by simp) i i'
  · intro h T hT i i'
    by_cases hne : T.Nonempty
    · obtain ⟨s₀, hs₀⟩ := hne
      classical
      let e := T.equivFin
      let servers : Fin t → S := fun k =>
        if hk : k.val < T.card then (e.symm ⟨k.val, hk⟩).1 else s₀
      have hrecover (idx : ι) :
          ProbComp.eval (P.coalitionQuery T idx) =
            (ProbComp.eval (P.tupleQuery servers idx)).map
              (fun f u => f ⟨(e u).val, (e u).isLt.trans_le hT⟩) := by
        rw [P.eval_coalitionQuery, P.eval_tupleQuery, PMF.map_comp]
        congr 1
        funext rq u
        change rq.2 u.1 = rq.2 (servers ⟨(e u).val, (e u).isLt.trans_le hT⟩)
        have hlt : (e u).val < T.card := (e u).isLt
        simp only [servers, dite_eq_left hlt, Fin.eta, Equiv.symm_apply_apply]
      rw [hrecover i, hrecover i', h servers i i']
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      exact P.isTPrivate_zero ∅ (by simp) i i'

theorem coalitionQuery_rows (ρ : Type) (P : Scheme ι S R Q A) (T : Finset S) (ji : ρ × ι) :
    (P.rows ρ).coalitionQuery T ji = P.coalitionQuery T ji.2 := by
  rw [coalitionQuery, query_rows, coalitionQuery]

theorem IsTPrivate.rows (ρ : Type) {t : ℕ} (h : P.IsTPrivate t) : (P.rows ρ).IsTPrivate t := by
  intro T hT ji ji'
  rw [coalitionQuery_rows, coalitionQuery_rows]
  exact h T hT ji.2 ji'.2

theorem coalitionQuery_comap {ι' : Type} (P : Scheme ι' S R Q A) (e : ι ↪ ι') (T : Finset S)
    (i : ι) : (P.comap e).coalitionQuery T i = P.coalitionQuery T (e i) := by
  rw [coalitionQuery, query_comap, coalitionQuery]

theorem IsTPrivate.comap {ι' : Type} {P : Scheme ι' S R Q A} {t : ℕ} (h : P.IsTPrivate t)
    (e : ι ↪ ι') : (P.comap e).IsTPrivate t := by
  intro T hT i i'
  rw [coalitionQuery_comap, coalitionQuery_comap]
  exact h T hT (e i) (e i')

/-! ### Full-coalition lower bound (`t ≥ |S|`) -/

/-- No zero-server scheme can be perfectly correct on a nonempty database index type. -/
theorem not_isCorrect_of_isEmpty [IsEmpty S] [Nonempty ι] (hcorrect : P.IsCorrect) : False := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨⟨r₀, q₀⟩, h₀⟩ := (ProbComp.eval (P.query i₀)).support_nonempty
  have hfalse := hcorrect.reconstruct_eq (fun _ => false) i₀ h₀
  have htrue := hcorrect.reconstruct_eq (fun _ => true) i₀ h₀
  have hans : (fun s => P.answer s (fun _ => false) (q₀ s)) =
      (fun s => P.answer s (fun _ => true) (q₀ s)) := funext isEmptyElim
  rw [hans] at hfalse
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

/-- When all servers can collude (`|S| ≤ t`), some joint query vector makes the combined server
answers determine the entire database, generalizing `SingleServer.exists_injective_answer`. -/
theorem exists_injective_answers_of_card_le [Fintype S] [Nonempty ι] {t : ℕ}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    ∃ q : S → Q, Function.Injective fun x s => P.answer s x (q s) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨⟨r₀, q₀⟩, h₀⟩ := (ProbComp.eval (P.query i₀)).support_nonempty
  refine ⟨q₀, fun x y hxy => funext fun i => ?_⟩
  have huniv : (Finset.univ : Finset S).card ≤ t := by simpa using hcard
  have hmem : (fun s : (Finset.univ : Finset S) => q₀ s.1) ∈
      (ProbComp.eval (P.coalitionQuery Finset.univ i)).support := by
    rw [hprivate Finset.univ huniv i i₀, P.eval_coalitionQuery]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨(r₀, q₀), h₀, rfl⟩
  rw [P.eval_coalitionQuery] at hmem
  obtain ⟨⟨r, q⟩, hrq, hq⟩ := (PMF.mem_support_map_iff _ _ _).1 hmem
  have hq_eq : q = q₀ := funext fun s => congrFun hq ⟨s, Finset.mem_univ s⟩
  have hans : (fun s => P.answer s x (q s)) = fun s => P.answer s y (q s) := by
    rw [hq_eq]
    exact hxy
  rw [← hcorrect.reconstruct_eq x i hrq, ← hcorrect.reconstruct_eq y i hrq, hans]

/-- A correct `t`-private scheme with `|S| ≤ t` satisfies `2 ^ |ι| ≤ |A| ^ |S|`. -/
theorem two_pow_card_le_card_answer_pow_of_card_le [Fintype S] [Nonempty ι] [Fintype ι] [Fintype A]
    {t : ℕ} (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    2 ^ Fintype.card ι ≤ Fintype.card A ^ Fintype.card S := by
  classical
  obtain ⟨q, hq⟩ := exists_injective_answers_of_card_le hcorrect hprivate hcard
  have h := Fintype.card_le_of_injective _ hq
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fun] at h

/-- **Necessity of `t < |S|`** (generalizing [CGKS, Section 5.1][ChorGoldreichKushilevitzSudan1998]
from `k = 1` to full coalitions `|S| ≤ t` under [Section 2.2][ChorGoldreichKushilevitzSudan1998]):
if all servers may collude (`|S| ≤ t`), any perfectly correct `t`-private scheme for `n`-bit
databases communicates at least `n` bits. -/
theorem card_le_communication_of_card_le [Fintype S] [Fintype ι] [Fintype Q] [Fintype A] {t : ℕ}
    (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) (hcard : Fintype.card S ≤ t) :
    Fintype.card ι ≤ communication S Q A := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Fintype.card_eq_zero]
    exact Nat.zero_le _
  · rcases isEmpty_or_nonempty S with hS | ⟨s₀⟩
    · exact (not_isCorrect_of_isEmpty hcorrect).elim
    · have hpow := two_pow_card_le_card_answer_pow_of_card_le hcorrect hprivate hcard
      have hclog : Fintype.card A ≤ 2 ^ Nat.clog 2 (Fintype.card A) :=
        Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card A)
      have hpow2 : 2 ^ Fintype.card ι ≤ 2 ^ (Fintype.card S * Nat.clog 2 (Fintype.card A)) := by
        calc 2 ^ Fintype.card ι ≤ Fintype.card A ^ Fintype.card S := hpow
          _ ≤ (2 ^ Nat.clog 2 (Fintype.card A)) ^ Fintype.card S :=
              Nat.pow_le_pow_left hclog _
          _ = 2 ^ (Fintype.card S * Nat.clog 2 (Fintype.card A)) := by
              rw [← pow_mul, Nat.mul_comm]
      have hle : Fintype.card ι ≤ Fintype.card S * Nat.clog 2 (Fintype.card A) := by
        by_contra hlt
        push Not at hlt
        have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
        omega
      rw [communication_eq]
      exact hle.trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))

end Scheme

/-! ### Existence of `t`-private schemes -/

/-- Some `k`-server scheme for databases indexed by `ι` is perfectly correct, perfectly `t`-private,
and communicates at most `c` bits. -/
def HasTPrivateScheme (ι : Type) (t k c : ℕ) : Prop :=
  ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : Scheme ι S R Q A),
    P.IsCorrect ∧ P.IsTPrivate t ∧ Fintype.card S = k ∧ communication S Q A ≤ c

theorem hasTPrivateScheme_iff {ι : Type} {t k c : ℕ} :
    HasTPrivateScheme ι t k c ↔
      ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : Scheme ι S R Q A),
        P.IsCorrect ∧ P.IsTPrivate t ∧ Fintype.card S = k ∧ communication S Q A ≤ c :=
  Iff.rfl

/-- `1`-private scheme existence agrees with `HasScheme`. -/
theorem hasTPrivateScheme_one_iff {ι : Type} {k c : ℕ} :
    HasTPrivateScheme ι 1 k c ↔ HasScheme ι k c := by
  simp only [hasTPrivateScheme_iff, hasScheme_iff, Scheme.isTPrivate_one_iff]

theorem Scheme.IsCorrect.hasTPrivateScheme {ι S R Q A : Type} [Fintype S] [Fintype Q] [Fintype A]
    {P : Scheme ι S R Q A} {t : ℕ} (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) :
    HasTPrivateScheme ι t (Fintype.card S) (communication S Q A) :=
  ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, rfl, le_rfl⟩

theorem HasTPrivateScheme.mono {ι : Type} {t k c c' : ℕ} (h : HasTPrivateScheme ι t k c)
    (hc : c ≤ c') : HasTPrivateScheme ι t k c' := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := h
  exact ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm.trans hc⟩

theorem HasTPrivateScheme.mono_threshold {ι : Type} {t₁ t₂ k c : ℕ} (ht : t₁ ≤ t₂)
    (h : HasTPrivateScheme ι t₂ k c) : HasTPrivateScheme ι t₁ k c := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := h
  exact ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate.mono ht, hk, hcomm⟩

theorem HasTPrivateScheme.hasScheme {ι : Type} {t k c : ℕ} (ht : 1 ≤ t)
    (h : HasTPrivateScheme ι t k c) : HasScheme ι k c :=
  hasTPrivateScheme_one_iff.mp (h.mono_threshold ht)

theorem HasTPrivateScheme.card_le_of_le {ι : Type} [Fintype ι] {t k c : ℕ}
    (h : HasTPrivateScheme ι t k c) (hkt : k ≤ t) : Fintype.card ι ≤ c := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := h
  exact (P.card_le_communication_of_card_le hcorrect hprivate (hk.trans_le hkt)).trans hcomm

/-! ### Linear and degree-`d` polynomial Shamir `t`-private PIR -/

section ShamirPIR

variable {F S : Type} [Field F] [Fintype F] [Fintype S]

/-- Linear Shamir `t`-private PIR over a finite field `F` ([Shamir1979];
[CGKS, Sections 1.1 and 2.2][ChorGoldreichKushilevitzSudan1998]): to read `x i`, the user shares
the indicator vector `j ↦ (if j = i then 1 else 0)` entrywise with independent degree-`t` Shamir
sharings, each server returns the field inner product with `x`, and the user reconstructs at `0`. -/
noncomputable def shamir (ι : Type) [Fintype ι] [DecidableEq ι] (params : Shamir.Params F S) :
    Scheme ι S Unit (ι → F) F where
  query i := do
    let r ← ProbComp.uniform (ι → Shamir.Randomness params)
    pure ((), fun s j => Shamir.share params (r j) (if j = i then 1 else 0) s)
  answer _ x a := ∑ j : ι, if x j then a j else 0
  reconstruct _ _ ans :=
    open scoped Classical in decide (Shamir.Polynomial.reconstruct params.point ans = 1)

/-- Degree-`d` polynomial `t`-private PIR on the cube `D → ι` ([Shamir1979];
[CGKS, Sections 1.1 and 2.2][ChorGoldreichKushilevitzSudan1998]): the user shares each coordinate
indicator `u ↦ (if u = i l then 1 else 0)` with degree `t = params.threshold`, each server returns
`∑ j, x j * ∏ l, a l (j l)` in `F` (evaluating a polynomial of degree at most `|D| * t` whose
constant term is `x i`), and the user interpolates the constant term from the `|S| > |D| * t`
server answers. -/
noncomputable def shamirCube (D ι : Type) [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (params : Shamir.Params F S) : Scheme (D → ι) S Unit (D → ι → F) F where
  query i := do
    let r ← ProbComp.uniform (D → ι → Shamir.Randomness params)
    pure ((), fun s l u => Shamir.share params (r l u) (if u = i l then 1 else 0) s)
  answer _ x a := ∑ j : D → ι, if x j then ∏ l : D, a l (j l) else 0
  reconstruct _ _ ans :=
    open scoped Classical in decide (Shamir.Polynomial.reconstruct params.point ans = 1)

/-- Sharing any vector `v : κ → F` entrywise with independent uniform Shamir randomness gives a
uniform joint view on `T → κ → F` for every unauthorized coalition `T.card ≤ params.threshold`,
reusing `Shamir.uniformOfFintype_map_restrict_share` coordinatewise via `PMF.pi`. -/
private theorem uniform_map_restrict_share_vec {κ : Type} [Fintype κ] [DecidableEq κ]
    [DecidableEq S] (params : Shamir.Params F S) (T : Finset S) (hT : T.card ≤ params.threshold)
    (v : κ → F) :
    (PMF.uniformOfFintype (κ → Shamir.Randomness params)).map
        (fun r (s : T) k => Shamir.share params (r k) (v k) s) =
      PMF.uniformOfFintype (T → κ → F) := by
  let flip : (κ → T → F) ≃ (T → κ → F) :=
    { toFun := fun g s k => g k s
      invFun := fun h k s => h s k
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpi :
      (PMF.uniformOfFintype (κ → Shamir.Randomness params)).map
          (fun r k (s : T) => Shamir.share params (r k) (v k) s) =
        PMF.uniformOfFintype (κ → T → F) := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype,
      ← Cslib.Probability.PMF.pi_map
        (fun _ : κ => PMF.uniformOfFintype (Shamir.Randomness params))
        (fun k coeffs (s : T) => Shamir.share params coeffs (v k) s)]
    simp only [Shamir.uniformOfFintype_map_restrict_share params T hT,
      Cslib.Probability.PMF.pi_uniformOfFintype]
  have hcomp :
      (fun (r : κ → Shamir.Randomness params) (s : T) k => Shamir.share params (r k) (v k) s) =
        flip ∘ fun (r : κ → Shamir.Randomness params) k (s : T) =>
          Shamir.share params (r k) (v k) s := rfl
  rw [hcomp, ← PMF.map_comp, hpi]
  exact PMF.uniformOfFintype_map_equiv flip

/-- Any coalition `T` of at most `params.threshold` servers in `PIR.shamir` sees a uniform family
of query vectors, independent of the queried index. -/
theorem eval_coalitionQuery_shamir {ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq S]
    (params : Shamir.Params F S) (T : Finset S) (hT : T.card ≤ params.threshold) (i : ι) :
    ProbComp.eval ((shamir ι params).coalitionQuery T i) = PMF.uniformOfFintype (T → ι → F) := by
  rw [Scheme.eval_coalitionQuery, shamir]
  simp only [pmf_norm, ProbComp.eval_uniform]
  exact uniform_map_restrict_share_vec params T hT (fun j => if j = i then 1 else 0)

/-- **Linear Shamir PIR is `t`-private** for `t = params.threshold`. -/
theorem isTPrivate_shamir {ι : Type} [Fintype ι] [DecidableEq ι] (params : Shamir.Params F S) :
    (shamir ι params).IsTPrivate params.threshold := by
  classical
  intro T hT i i'
  rw [eval_coalitionQuery_shamir params T hT i, eval_coalitionQuery_shamir params T hT i']

/-- **Linear Shamir PIR is perfectly correct**: Lagrange reconstruction at `0` recovers `1` when
`x i = true` and `0` when `x i = false`. -/
theorem isCorrect_shamir {ι : Type} [Fintype ι] [DecidableEq ι] (params : Shamir.Params F S) :
    (shamir ι params).IsCorrect := by
  classical
  rw [Scheme.isCorrect_iff]
  intro x i _ q hrq
  simp only [shamir, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨r, -, -, rfl⟩ := hrq
  let sec : ι → F := fun j => if x j then (if j = i then 1 else 0) else 0
  let coeff : ι → Shamir.Randomness params := fun j => if x j then r j else 0
  have hans :
      (fun s : S =>
        ∑ j : ι, if x j then Shamir.share params (r j) (if j = i then 1 else 0) s else 0) =
        fun s : S => Shamir.share params (∑ j : ι, coeff j) (∑ j : ι, sec j) s := by
    funext s
    rw [Shamir.share_sum Finset.univ params coeff sec s]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hxj : x j <;> simp [coeff, sec, hxj]
  dsimp only [shamir]
  rw [hans, Shamir.Polynomial.reconstruct_share_eq_secret params]
  have hsum : ∑ j : ι, sec j = if x i then 1 else 0 := by
    simp only [sec]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hsum]
  cases x i <;> simp

omit [Fintype F] [Fintype S] in
private theorem ne_of_map_eq_pure_one_zero {α : Type} {p q : PMF α} (f : α → F)
    (hp : p.map f = PMF.pure 1) (hq : q.map f = PMF.pure 0) : p ≠ q := by
  intro heq
  rw [heq, hq] at hp
  have hsupp := congrArg PMF.support hp
  rw [PMF.support_pure, PMF.support_pure, Set.singleton_eq_singleton_iff] at hsupp
  exact zero_ne_one hsupp

/-- **Sharpness of the collusion threshold**: `(params.threshold + 1)` servers are authorized in
Shamir secret sharing and can reconstruct the target index, so `PIR.shamir` is not
`(params.threshold + 1)`-private on any nontrivial database index type (`|ι| ≥ 2`). -/
theorem not_isTPrivate_succ_shamir {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (params : Shamir.Params F S) :
    ¬ (shamir ι params).IsTPrivate (params.threshold + 1) := by
  intro hpriv
  obtain ⟨i₀, i₁, hne⟩ := exists_pair_ne ι
  obtain ⟨T, -, hcard⟩ :=
    Finset.exists_subset_card_eq (Nat.succ_le_of_lt params.threshold_lt_card)
  have hT : Shamir.authorized params T := by rw [Shamir.authorized, hcard]
  have hrec (idx : ι) :
      (ProbComp.eval ((shamir ι params).coalitionQuery T idx)).map
          (fun (qT : T → ι → F) => Shamir.reconstruct params T (fun s => qT s i₀)) =
        PMF.pure (if i₀ = idx then (1 : F) else 0) := by
    rw [Scheme.eval_coalitionQuery, shamir, ProbComp.eval_bind]
    simp only [ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind, PMF.pure_map,
      Shamir.reconstruct_share_eq_secret params _ _ hT, PMF.bind_const]
  refine ne_of_map_eq_pure_one_zero
    (fun (qT : T → ι → F) => Shamir.reconstruct params T (fun s => qT s i₀))
    (by rw [hrec i₀, ite_eq_left rfl]) (by rw [hrec i₁, ite_eq_right hne])
    (hpriv T hcard.le i₀ i₁)

/-- Any coalition `T` of at most `params.threshold` servers in `PIR.shamirCube` sees uniform
coordinate query tables, independent of the target cube point. -/
theorem eval_coalitionQuery_shamirCube {D ι : Type} [Fintype D] [DecidableEq D]
    [Fintype ι] [DecidableEq ι] [DecidableEq S] (params : Shamir.Params F S)
    (T : Finset S) (hT : T.card ≤ params.threshold) (i : D → ι) :
    ProbComp.eval ((shamirCube D ι params).coalitionQuery T i) =
      PMF.uniformOfFintype (T → D → ι → F) := by
  rw [Scheme.eval_coalitionQuery, shamirCube]
  simp only [pmf_norm, ProbComp.eval_uniform]
  change (PMF.uniformOfFintype (D → ι → Shamir.Randomness params)).map
    (fun r (s : T) l u => Shamir.share params (r l u) (if u = i l then 1 else 0) s) = _
  let cur : ((D × ι) → Shamir.Randomness params) ≃ (D → ι → Shamir.Randomness params) :=
    Equiv.curry D ι (Shamir.Randomness params)
  let outCur : (T → (D × ι) → F) ≃ (T → D → ι → F) :=
    Equiv.arrowCongr (Equiv.refl T) (Equiv.curry D ι F)
  rw [← PMF.uniformOfFintype_map_equiv cur, PMF.map_comp]
  have hcomp :
      ((fun (r : D → ι → Shamir.Randomness params) (s : T) l u =>
          Shamir.share params (r l u) (if u = i l then 1 else 0) s) ∘ cur) =
        outCur ∘ (fun (r : (D × ι) → Shamir.Randomness params) (s : T) lu =>
          Shamir.share params (r lu) (if lu.2 = i lu.1 then 1 else 0) s) := rfl
  rw [hcomp, ← PMF.map_comp,
    uniform_map_restrict_share_vec params T hT (fun lu : D × ι => if lu.2 = i lu.1 then 1 else 0)]
  exact PMF.uniformOfFintype_map_equiv outCur

/-- **Degree-`d` polynomial PIR is `t`-private** for `t = params.threshold`. -/
theorem isTPrivate_shamirCube {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (params : Shamir.Params F S) :
    (shamirCube D ι params).IsTPrivate params.threshold := by
  classical
  intro T hT i i'
  rw [eval_coalitionQuery_shamirCube params T hT i, eval_coalitionQuery_shamirCube params T hT i']

/-- **Sharpness of the collusion threshold for `PIR.shamirCube`**: even when `|S| > |D| * t`
servers are used for degree-`d t` reconstruction, any `params.threshold + 1` colluding servers can
reconstruct coordinate indicators and learn `i`, so `PIR.shamirCube` is not
`(params.threshold + 1)`-private whenever `D` is nonempty and `ι` is nontrivial. -/
theorem not_isTPrivate_succ_shamirCube {D ι : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    [Fintype ι] [DecidableEq ι] [Nontrivial ι] (params : Shamir.Params F S) :
    ¬ (shamirCube D ι params).IsTPrivate (params.threshold + 1) := by
  intro hpriv
  obtain ⟨l₀⟩ := ‹Nonempty D›
  obtain ⟨u₀, u₁, hne⟩ := exists_pair_ne ι
  obtain ⟨T, -, hcard⟩ :=
    Finset.exists_subset_card_eq (Nat.succ_le_of_lt params.threshold_lt_card)
  have hT : Shamir.authorized params T := by rw [Shamir.authorized, hcard]
  have hrec (idx : D → ι) :
      (ProbComp.eval ((shamirCube D ι params).coalitionQuery T idx)).map
          (fun (qT : T → D → ι → F) => Shamir.reconstruct params T (fun s => qT s l₀ u₀)) =
        PMF.pure (if u₀ = idx l₀ then (1 : F) else 0) := by
    rw [Scheme.eval_coalitionQuery, shamirCube, ProbComp.eval_bind]
    simp only [ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind, PMF.pure_map,
      Shamir.reconstruct_share_eq_secret params _ _ hT, PMF.bind_const]
  refine ne_of_map_eq_pure_one_zero
    (fun (qT : T → D → ι → F) => Shamir.reconstruct params T (fun s => qT s l₀ u₀))
    (by rw [hrec (fun _ => u₀), ite_eq_left rfl]) (by rw [hrec (fun _ => u₁), ite_eq_right hne])
    (hpriv T hcard.le (fun _ => u₀) (fun _ => u₁))

/-- **Degree-`d` polynomial PIR is perfectly correct** whenever `|D| * params.threshold < |S|`:
each server evaluates a polynomial of degree at most `|D| * t` whose constant term is `1` if `x i`
and `0` otherwise. -/
theorem isCorrect_shamirCube {D ι : Type} [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (params : Shamir.Params F S) (hdeg : Fintype.card D * params.threshold < Fintype.card S) :
    (shamirCube D ι params).IsCorrect := by
  classical
  rw [Scheme.isCorrect_iff]
  intro x i _ q hrq
  simp only [shamirCube, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨r, -, -, rfl⟩ := hrq
  let factor (l : D) (u : ι) : _root_.Polynomial F :=
    Shamir.Polynomial.sharingPolynomial (if u = i l then 1 else 0)
      (Shamir.Polynomial.tailPolynomial params.threshold (r l u))
  let term (j : D → ι) : _root_.Polynomial F :=
    if x j then ∏ l : D, factor l (j l) else 0
  let poly : _root_.Polynomial F := ∑ j : D → ι, term j
  have heval (s : S) :
      poly.eval (params.point s) =
        ∑ j : D → ι,
          if x j then
            ∏ l : D, Shamir.share params (r l (j l)) (if j l = i l then 1 else 0) s
          else 0 := by
    simp only [poly, term, _root_.Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hxj : x j
    · simp only [hxj, ↓reduceIte, _root_.Polynomial.eval_prod, factor, Shamir.share]
    · simp [hxj]
  have hfactor_deg (l : D) (u : ι) : (factor l u).natDegree ≤ params.threshold :=
    Shamir.Polynomial.natDegree_sharingPolynomial_le _ _
      (Shamir.Polynomial.tailPolynomial_degree_lt _ _)
  have hterm_deg (j : D → ι) : (term j).natDegree ≤ Fintype.card D * params.threshold := by
    by_cases hxj : x j
    · simp only [term, hxj, ↓reduceIte]
      refine (_root_.Polynomial.natDegree_prod_le _ _).trans ?_
      simpa using Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hfactor_deg l (j l)
    · simp [term, hxj]
  have hpoly_deg : poly.degree < Fintype.card S := by
    have hnat : poly.natDegree ≤ Fintype.card D * params.threshold :=
      _root_.Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => hterm_deg j
    refine _root_.Polynomial.degree_le_natDegree.trans_lt ?_
    exact_mod_cast hnat.trans_lt hdeg
  have hconst : poly.constantCoeff = if x i then 1 else 0 := by
    simp only [poly, term, map_sum _root_.Polynomial.constantCoeff]
    rw [Finset.sum_eq_single i]
    · by_cases hxi : x i
      · simp only [hxi, ↓reduceIte, map_prod _root_.Polynomial.constantCoeff, factor,
          Shamir.Polynomial.constantCoeff_sharingPolynomial, Finset.prod_const_one]
      · simp [hxi]
    · intro j _ hji
      obtain ⟨l₀, hl₀⟩ := Function.ne_iff.mp hji
      by_cases hxj : x j
      · simp only [hxj, ↓reduceIte, map_prod _root_.Polynomial.constantCoeff]
        refine Finset.prod_eq_zero (Finset.mem_univ l₀) ?_
        dsimp only [factor]
        rw [ite_eq_right hl₀, Shamir.Polynomial.constantCoeff_sharingPolynomial]
      · simp [hxj]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hans :
      (fun s : S =>
        ∑ j : D → ι,
          if x j then
            ∏ l : D, Shamir.share params (r l (j l)) (if j l = i l then 1 else 0) s
          else 0) =
        fun s : S => poly.eval (params.point s) :=
    funext fun s => (heval s).symm
  dsimp only [shamirCube]
  rw [hans,
    Shamir.Polynomial.reconstruct_eq_constantCoeff_of_eval_eq params.point_injective hpoly_deg,
    hconst]
  cases x i <;> simp

end ShamirPIR

section ShamirCommunication

/-- Communication upper bound for `shamirCube`: each server receives `|D| * |ι|` field elements and
sends `1` field element. -/
theorem communication_shamirCube_le {F S D ι : Type} [Fintype F] [Fintype S]
    [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι] :
    communication S (D → ι → F) F ≤
      Fintype.card S * ((Fintype.card D * Fintype.card ι + 1) * Nat.clog 2 (Fintype.card F)) := by
  rw [communication_eq]
  simp only [Fintype.card_fun]
  rw [← pow_mul, Nat.mul_comm (Fintype.card ι)]
  have hclog := clog_pow_le_mul (Fintype.card D * Fintype.card ι) (Fintype.card F)
  nlinarith

/-- Communication upper bound for `rows`-balanced `shamirCube`
([CGKS, Section 3.4, p. 11][ChorGoldreichKushilevitzSudan1998]): each server receives `|D| * |ι|`
field elements and sends `|ρ|` field elements. -/
theorem communication_shamirCube_rows_le {F S ρ D ι : Type} [Fintype F] [Fintype S]
    [Fintype ρ] [DecidableEq ρ] [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι] :
    communication S (D → ι → F) (ρ → F) ≤
      Fintype.card S *
        ((Fintype.card D * Fintype.card ι + Fintype.card ρ) * Nat.clog 2 (Fintype.card F)) := by
  rw [communication_eq]
  simp only [Fintype.card_fun]
  rw [← pow_mul, Nat.mul_comm (Fintype.card ι)]
  have hQ := clog_pow_le_mul (Fintype.card D * Fintype.card ι) (Fintype.card F)
  have hA := clog_pow_le_mul (Fintype.card ρ) (Fintype.card F)
  nlinarith

/-- Communication upper bound for matrix-balanced linear Shamir PIR (`(shamir ι params).rows ρ`). -/
theorem communication_shamir_rows_le {F S ρ ι : Type} [Fintype F] [Fintype S]
    [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι] :
    communication S (ι → F) (ρ → F) ≤
      Fintype.card S * ((Fintype.card ι + Fintype.card ρ) * Nat.clog 2 (Fintype.card F)) := by
  rw [communication_eq]
  simp only [Fintype.card_fun]
  have hQ := clog_pow_le_mul (Fintype.card ι) (Fintype.card F)
  have hA := clog_pow_le_mul (Fintype.card ρ) (Fintype.card F)
  nlinarith

end ShamirCommunication

section ShamirBounds

variable {F S : Type} [Field F] [Fintype F] [Fintype S]

/-- **`(t + 1)`-server `O(√n)` `t`-private PIR**: applying `Scheme.rows` to `PIR.shamir` solves any
`n ≤ m ^ 2` with `|S|` servers (`params.threshold < |S|`) and `|S| * 2 m * ⌈log₂ |F|⌉` bits. -/
theorem hasTPrivateScheme_of_le_mul_self (params : Shamir.Params F S) {n m : ℕ}
    (h : n ≤ m * m) :
    HasTPrivateScheme (Fin n) params.threshold (Fintype.card S)
      (Fintype.card S * (2 * m * Nat.clog 2 (Fintype.card F))) := by
  classical
  let e : Fin n ↪ Fin m × Fin m := (Fin.castLEEmb h).trans finProdFinEquiv.symm.toEmbedding
  have hP := ((isCorrect_shamir (ι := Fin m) params).rows (Fin m)).comap e
    |>.hasTPrivateScheme (((isTPrivate_shamir (ι := Fin m) params).rows (Fin m)).comap e)
  refine hP.mono ?_
  have hcomm := communication_shamir_rows_le (F := F) (S := S) (ρ := Fin m) (ι := Fin m)
  simp only [Fintype.card_fin] at hcomm
  linarith

/-- **Unbalanced `(d t + 1)`-server `O(n ^ (1 / d))` `t`-private PIR**: whenever
`d * params.threshold < |S|` and `n ≤ ℓ ^ d`, `PIR.shamirCube` gives a perfectly correct `t`-private
scheme communicating at most `|S| * ((d * ℓ + 1) * ⌈log₂ |F|⌉)` bits. -/
theorem hasTPrivateScheme_of_le_pow (params : Shamir.Params F S) {n d ℓ : ℕ}
    (hdeg : d * params.threshold < Fintype.card S) (h : n ≤ ℓ ^ d) :
    HasTPrivateScheme (Fin n) params.threshold (Fintype.card S)
      (Fintype.card S * ((d * ℓ + 1) * Nat.clog 2 (Fintype.card F))) := by
  classical
  let e : Fin n ↪ (Fin d → Fin ℓ) :=
    (Fin.castLEEmb h).trans finFunctionFinEquiv.symm.toEmbedding
  have hdeg' : Fintype.card (Fin d) * params.threshold < Fintype.card S := by
    simpa using hdeg
  have hP := (isCorrect_shamirCube (D := Fin d) (ι := Fin ℓ) params hdeg').comap e
    |>.hasTPrivateScheme ((isTPrivate_shamirCube (D := Fin d) (ι := Fin ℓ) params).comap e)
  refine hP.mono ?_
  have hcomm := communication_shamirCube_le (F := F) (S := S) (D := Fin d) (ι := Fin ℓ)
  simpa only [Fintype.card_fin] using hcomm

/-- **Balanced `c t`-server `O(n ^ (1 / c))` `t`-private PIR**
([CGKS, Sections 1.1 and 3.4, p. 11][ChorGoldreichKushilevitzSudan1998]): applying `Scheme.rows`
(`Fin ℓ`) to `PIR.shamirCube (Fin d) (Fin ℓ)` solves any `n ≤ ℓ ^ (d + 1)` whenever
`d * params.threshold < |S|`, using `|S| * ((d + 1) * ℓ * ⌈log₂ |F|⌉)` bits. For `c = d + 1 ≥ 2` and
`t = params.threshold ≥ 1`, `(c - 1) * t < c * t` holds with **exact `|S| = c * t` servers**. -/
theorem hasTPrivateScheme_rows_of_le_pow (params : Shamir.Params F S) {n d ℓ : ℕ}
    (hdeg : d * params.threshold < Fintype.card S) (h : n ≤ ℓ ^ (d + 1)) :
    HasTPrivateScheme (Fin n) params.threshold (Fintype.card S)
      (Fintype.card S * ((d + 1) * ℓ * Nat.clog 2 (Fintype.card F))) := by
  classical
  have hsplit : n ≤ ℓ * ℓ ^ d := by simpa [pow_succ'] using h
  let eProd : Fin n ↪ Fin ℓ × Fin (ℓ ^ d) :=
    (Fin.castLEEmb hsplit).trans finProdFinEquiv.symm.toEmbedding
  let e : Fin n ↪ Fin ℓ × (Fin d → Fin ℓ) :=
    eProd.trans (Equiv.prodCongr (Equiv.refl (Fin ℓ)) finFunctionFinEquiv.symm).toEmbedding
  have hdeg' : Fintype.card (Fin d) * params.threshold < Fintype.card S := by
    simpa using hdeg
  have hP := ((isCorrect_shamirCube (D := Fin d) (ι := Fin ℓ) params hdeg').rows (Fin ℓ)).comap e
    |>.hasTPrivateScheme
      (((isTPrivate_shamirCube (D := Fin d) (ι := Fin ℓ) params).rows (Fin ℓ)).comap e)
  refine hP.mono ?_
  have hcomm :=
    communication_shamirCube_rows_le (F := F) (S := S) (ρ := Fin ℓ) (D := Fin d) (ι := Fin ℓ)
  simp only [Fintype.card_fin] at hcomm
  nlinarith

end ShamirBounds

/-- Canonical Shamir parameters for `k` servers over `ZMod p` using evaluation points `1, …, k`
when `t < k < p` for a prime `p`. -/
def zmodShamirParams {t k p : ℕ} [Fact p.Prime] (htk : t < k) (hkp : k < p) :
    Shamir.Params (ZMod p) (Fin k) where
  threshold := t
  threshold_lt_card := by simpa using htk
  point s := ((s.val + 1 : ℕ) : ZMod p)
  point_injective := by
    intro s₁ s₂ h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext (by omega)
  point_nonzero s := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega

@[simp] theorem threshold_zmodShamirParams {t k p : ℕ} [Fact p.Prime] (htk : t < k) (hkp : k < p) :
    (zmodShamirParams htk hkp).threshold = t := by
  rw [zmodShamirParams]

@[simp] theorem point_zmodShamirParams {t k p : ℕ} [Fact p.Prime] (htk : t < k) (hkp : k < p)
    (s : Fin k) : (zmodShamirParams htk hkp).point s = ((s.val + 1 : ℕ) : ZMod p) := by
  rw [zmodShamirParams]

/-- Concrete prime-field `t`-private `k`-server polynomial PIR for `d * t < k < p` and
`n ≤ ℓ ^ d`. -/
theorem hasTPrivateScheme_prime_of_le_pow {n d ℓ t k p : ℕ} [Fact p.Prime]
    (hdeg : d * t < k) (hd : 0 < d) (hkp : k < p) (hn : n ≤ ℓ ^ d) :
    HasTPrivateScheme (Fin n) t k (k * ((d * ℓ + 1) * Nat.clog 2 p)) := by
  have htk : t < k := (Nat.le_mul_of_pos_left t hd).trans_lt hdeg
  have h := hasTPrivateScheme_of_le_pow (zmodShamirParams htk hkp) (by simpa using hdeg) hn
  simpa [ZMod.card] using h

/-- Concrete prime-field `rows`-balanced `t`-private `k`-server polynomial PIR for `d * t < k < p`
and `n ≤ ℓ ^ (d + 1)` ([CGKS, Sections 1.1 and 3.4][ChorGoldreichKushilevitzSudan1998], achieving
exact `k = c * t` servers at `d = c - 1` when `1 < c` and `0 < t`). -/
theorem hasTPrivateScheme_prime_rows_of_le_pow {n d ℓ t k p : ℕ} [Fact p.Prime]
    (htk : t < k) (hdeg : d * t < k) (hkp : k < p) (hn : n ≤ ℓ ^ (d + 1)) :
    HasTPrivateScheme (Fin n) t k (k * ((d + 1) * ℓ * Nat.clog 2 p)) := by
  have h := hasTPrivateScheme_rows_of_le_pow (zmodShamirParams htk hkp) (by simpa using hdeg) hn
  simpa [ZMod.card] using h

end Cslib.Crypto.Protocols.PIR
