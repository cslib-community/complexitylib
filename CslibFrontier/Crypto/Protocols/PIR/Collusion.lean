/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Basic

/-!
# Coalition-private information retrieval and full-coalition lower bounds

[Chor, Goldreich, Kushilevitz and Sudan, Section 2.2, pp. 4–5][ChorGoldreichKushilevitzSudan1998]
extends one-round private information retrieval from single curious servers to coalitions of up to
`t` colluding servers: for every coalition of at most `t` servers, the joint distribution of the
queries sent to those servers does not depend on the target index `i`.

* **Coalition privacy (`Scheme.IsTPrivate`).** `P.coalitionQuery T i` projects the joint query draw
  onto `T : Finset S`, and `P.IsTPrivate t` asks its law to be independent of `i` whenever
  `T.card ≤ t` (for arbitrary entry payload type `β`, defaulting to `Bool`). At `t = 0` this holds
  trivially (`Scheme.isTPrivate_zero`), at `t = 1` it is equivalent to single-server
  `Scheme.IsPrivate` (`Scheme.isTPrivate_one_iff`), and for every `t` it is equivalent to the
  paper's `t`-tuple formulation (`Scheme.isTPrivate_iff_tuple`). `Scheme.IsTPrivate.of_query_eq`
  transfers it to every scheme whose queries have the law of the queries of a `t`-private scheme
  up to reindexing, such as `Scheme.rows` and `Scheme.comap`.
* **Existence (`HasTPrivateScheme`, `HasScheme`).** `HasTPrivateScheme ι t k c β` says that a
  correct, `t`-private `k`-server scheme communicating at most `c` bits exists; the single-server
  statement `HasScheme ι k c β` is its `t = 1` case, unfolded by `hasScheme_iff`.
  `HasTPrivateScheme.fin_of_le_card` turns a scheme for a grid or a cube into one for `Fin n`.
* **Necessity of `t < |S|` (`Scheme.exists_injective_answers_of_card_le`,
  `Scheme.card_le_communication_of_card_le`).** Generalizing the single-server injectivity argument
  of [CGKS, Section 5.1, p. 14][ChorGoldreichKushilevitzSudan1998] (`PIR.SingleServer`) from
  `|S| = 1` to full coalitions `|S| ≤ t`, the entire query tuple has an index-independent law, so
  some joint query vector makes the combined server answer map injective on the database
  (`|β| ^ |ι| ≤ |A| ^ |S|`) and forces at least `|ι|` bits of communication for Boolean databases
  (with no correct zero-server scheme on nonempty databases over nontrivial payloads).

Polynomial Shamir `t`-private constructions live in `PIR.Shamir`, single-server specializations in
`PIR.SingleServer`, and block-retrieval transformations in `PIR.Block`.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Scheme.coalitionQuery`,
  `Cslib.Crypto.Protocols.PIR.Scheme.tupleQuery`: joint query marginals on server subsets and
  tuples.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate`: perfect information-theoretic `t`-privacy.
* `Cslib.Crypto.Protocols.PIR.HasTPrivateScheme`, `Cslib.Crypto.Protocols.PIR.HasScheme`:
  existence of a correct, `t`-private (respectively private) `k`-server scheme within a bit budget.

## Main results

* `Cslib.Crypto.Protocols.PIR.Scheme.isTPrivate_one_iff`,
  `Cslib.Crypto.Protocols.PIR.Scheme.isTPrivate_iff_tuple`: equivalence with `IsPrivate` at `t = 1`
  and with `t`-tuple query independence.
* `Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate.of_query_eq`: `t`-privacy transfers along
  reindexed query laws.
* `Cslib.Crypto.Protocols.PIR.hasScheme_iff`: `HasScheme` unfolded with single-server privacy.
* `Cslib.Crypto.Protocols.PIR.HasTPrivateScheme.comap`,
  `Cslib.Crypto.Protocols.PIR.HasTPrivateScheme.fin_of_le_card`: existence restricts along an
  embedding of indices, in particular to `Fin n` from any index type with at least `n` elements.
* `Cslib.Crypto.Protocols.PIR.Scheme.exists_injective_answers_of_card_le`,
  `Cslib.Crypto.Protocols.PIR.Scheme.card_le_communication_of_card_le`: full-coalition `|S| ≤ t`
  determines the database from one joint answer vector and requires at least `|ι|` bits.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Sections 2.2 and 5.1 (pp. 4–5 and 14); numbering
  of the authors' journal version of April 21, 1998
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability

namespace Scheme

variable {ι S R Q A β : Type}

section CoalitionDefs

variable (P : Scheme ι S R Q A β)

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

variable {P : Scheme ι S R Q A β}

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

/-- **`t`-privacy transfer.** If the queries that `P'` sends for `i` have the law of the queries
that the `t`-private scheme `P` sends for `f i`, then `P'` is `t`-private. The retained states,
answers and reconstructions of the two schemes are unconstrained. -/
theorem IsTPrivate.of_query_eq {ι' R' A' β' : Type} {P' : Scheme ι' S R' Q A' β'} {t : ℕ}
    (h : P.IsTPrivate t) (f : ι' → ι)
    (hq : ∀ i,
      ProbComp.eval (Prod.snd <$> P'.query i) = ProbComp.eval (Prod.snd <$> P.query (f i))) :
    P'.IsTPrivate t := by
  have hview (T : Finset S) (i : ι') :
      ProbComp.eval (P'.coalitionQuery T i) = ProbComp.eval (P.coalitionQuery T (f i)) := by
    have hT := congrArg (PMF.map fun q (s : T) => q s) (hq i)
    simp only [ProbComp.eval_map, PMF.map_comp] at hT
    rw [eval_coalitionQuery, eval_coalitionQuery]
    exact hT
  exact fun T hT i i' => by rw [hview, hview, h.eval_coalitionQuery_eq T hT]

theorem IsTPrivate.rows (ρ : Type) {t : ℕ} (h : P.IsTPrivate t) : (P.rows ρ).IsTPrivate t :=
  h.of_query_eq Prod.snd fun _ => by rw [query_rows]

theorem IsTPrivate.comap {ι' : Type} {P : Scheme ι' S R Q A β} {t : ℕ} (h : P.IsTPrivate t)
    (e : ι ↪ ι') (pad : β) : (P.comap e pad).IsTPrivate t :=
  h.of_query_eq e fun _ => by rw [query_comap]

/-! ### Full-coalition lower bound (`t ≥ |S|`) -/

/-- No zero-server scheme can be perfectly correct on a nonempty database index type over a
nontrivial payload alphabet. -/
theorem not_isCorrect_of_isEmpty [IsEmpty S] [Nonempty ι] [Nontrivial β]
    (hcorrect : P.IsCorrect) : False := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨b₀, b₁, hne⟩ := exists_pair_ne β
  obtain ⟨⟨r₀, q₀⟩, h₀⟩ := (ProbComp.eval (P.query i₀)).support_nonempty
  have hb₀ := hcorrect.reconstruct_eq (fun _ => b₀) i₀ h₀
  have hb₁ := hcorrect.reconstruct_eq (fun _ => b₁) i₀ h₀
  have hans : (fun s => P.answer s (fun _ => b₀) (q₀ s)) =
      (fun s => P.answer s (fun _ => b₁) (q₀ s)) := funext isEmptyElim
  rw [hans] at hb₀
  exact hne (hb₀.symm.trans hb₁)

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

/-- A correct `t`-private Boolean scheme with `|S| ≤ t` satisfies `2 ^ |ι| ≤ |A| ^ |S|`. -/
theorem two_pow_card_le_card_answer_pow_of_card_le [Fintype S] [Nonempty ι] [Fintype ι] [Fintype A]
    {P : Scheme ι S R Q A} {t : ℕ} (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t)
    (hcard : Fintype.card S ≤ t) : 2 ^ Fintype.card ι ≤ Fintype.card A ^ Fintype.card S := by
  classical
  obtain ⟨q, hq⟩ := exists_injective_answers_of_card_le hcorrect hprivate hcard
  have h := Fintype.card_le_of_injective _ hq
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fun] at h

/-- **Necessity of `t < |S|`** (generalizing
[CGKS, Section 5.1, p. 14][ChorGoldreichKushilevitzSudan1998] from `k = 1` to full coalitions
`|S| ≤ t` under [Section 2.2][ChorGoldreichKushilevitzSudan1998]): if all servers may collude
(`|S| ≤ t`), any perfectly correct `t`-private scheme for `n`-bit databases communicates at least
`n` bits. -/
theorem card_le_communication_of_card_le [Fintype S] [Fintype ι] [Fintype Q] [Fintype A]
    {P : Scheme ι S R Q A} {t : ℕ} (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t)
    (hcard : Fintype.card S ≤ t) : Fintype.card ι ≤ communication S Q A := by
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

/-- Some `k`-server scheme for databases `ι → β` (by default `β = Bool`) is perfectly correct,
perfectly `t`-private, and communicates at most `c` bits. -/
def HasTPrivateScheme (ι : Type) (t k c : ℕ) (β : Type := Bool) : Prop :=
  ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : Scheme ι S R Q A β),
    P.IsCorrect ∧ P.IsTPrivate t ∧ Fintype.card S = k ∧ communication S Q A ≤ c

/-- Some `k`-server scheme for databases `ι → β` (by default `β = Bool`) is perfectly correct and
perfectly private and communicates at most `c` bits: the `t = 1` case of `HasTPrivateScheme`, by
`Scheme.isTPrivate_one_iff`. `hasScheme_iff` states it with `Scheme.IsPrivate`. -/
def HasScheme (ι : Type) (k c : ℕ) (β : Type := Bool) : Prop :=
  HasTPrivateScheme ι 1 k c β

theorem hasTPrivateScheme_iff {ι β : Type} {t k c : ℕ} :
    HasTPrivateScheme ι t k c β ↔
      ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : Scheme ι S R Q A β),
        P.IsCorrect ∧ P.IsTPrivate t ∧ Fintype.card S = k ∧ communication S Q A ≤ c := by
  rw [HasTPrivateScheme]

/-- `1`-private scheme existence is `HasScheme`. -/
theorem hasTPrivateScheme_one_iff {ι β : Type} {k c : ℕ} :
    HasTPrivateScheme ι 1 k c β ↔ HasScheme ι k c β :=
  Iff.rfl

theorem hasScheme_iff {ι β : Type} {k c : ℕ} : HasScheme ι k c β ↔
    ∃ (S R Q A : Type) (_ : Fintype S) (_ : Fintype Q) (_ : Fintype A) (P : Scheme ι S R Q A β),
      P.IsCorrect ∧ P.IsPrivate ∧ Fintype.card S = k ∧ communication S Q A ≤ c := by
  simp only [← hasTPrivateScheme_one_iff, hasTPrivateScheme_iff, Scheme.isTPrivate_one_iff]

theorem Scheme.IsCorrect.hasTPrivateScheme {ι S R Q A β : Type} [Fintype S] [Fintype Q] [Fintype A]
    {P : Scheme ι S R Q A β} {t : ℕ} (hcorrect : P.IsCorrect) (hprivate : P.IsTPrivate t) :
    HasTPrivateScheme ι t (Fintype.card S) (communication S Q A) β :=
  hasTPrivateScheme_iff.mpr ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, rfl, le_rfl⟩

/-- A correct, private scheme witnesses `HasScheme`. -/
theorem Scheme.IsCorrect.hasScheme {ι S R Q A β : Type} [Fintype S] [Fintype Q] [Fintype A]
    {P : Scheme ι S R Q A β} (hcorrect : P.IsCorrect) (hprivate : P.IsPrivate) :
    HasScheme ι (Fintype.card S) (communication S Q A) β :=
  hcorrect.hasTPrivateScheme (Scheme.isTPrivate_one_iff.mpr hprivate)

theorem HasTPrivateScheme.mono {ι β : Type} {t k c c' : ℕ} (h : HasTPrivateScheme ι t k c β)
    (hc : c ≤ c') : HasTPrivateScheme ι t k c' β := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := hasTPrivateScheme_iff.mp h
  exact hasTPrivateScheme_iff.mpr ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm.trans hc⟩

theorem HasScheme.mono {ι β : Type} {k c c' : ℕ} (h : HasScheme ι k c β) (hc : c ≤ c') :
    HasScheme ι k c' β :=
  HasTPrivateScheme.mono h hc

theorem HasTPrivateScheme.mono_threshold {ι β : Type} {t₁ t₂ k c : ℕ} (ht : t₁ ≤ t₂)
    (h : HasTPrivateScheme ι t₂ k c β) : HasTPrivateScheme ι t₁ k c β := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := hasTPrivateScheme_iff.mp h
  exact hasTPrivateScheme_iff.mpr ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate.mono ht, hk, hcomm⟩

theorem HasTPrivateScheme.hasScheme {ι β : Type} {t k c : ℕ} (ht : 1 ≤ t)
    (h : HasTPrivateScheme ι t k c β) : HasScheme ι k c β :=
  h.mono_threshold ht

/-- A scheme for a larger index type restricts along an embedding `ι ↪ ι'`
(`Scheme.comap`), keeping its servers and communication. -/
theorem HasTPrivateScheme.comap {ι ι' β : Type} [Nonempty β] {t k c : ℕ}
    (h : HasTPrivateScheme ι' t k c β) (e : ι ↪ ι') : HasTPrivateScheme ι t k c β := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := hasTPrivateScheme_iff.mp h
  let pad : β := Classical.arbitrary β
  exact hasTPrivateScheme_iff.mpr
    ⟨S, R, Q, A, _, _, _, P.comap e pad, hcorrect.comap e pad, hprivate.comap e pad, hk, hcomm⟩

theorem HasScheme.comap {ι ι' β : Type} [Nonempty β] {k c : ℕ} (h : HasScheme ι' k c β)
    (e : ι ↪ ι') : HasScheme ι k c β :=
  HasTPrivateScheme.comap h e

/-- A scheme for a finite index type of size at least `n` gives one for `n`-entry databases. -/
theorem HasTPrivateScheme.fin_of_le_card {ι β : Type} [Fintype ι] [Nonempty β] {n t k c : ℕ}
    (h : HasTPrivateScheme ι t k c β) (hn : n ≤ Fintype.card ι) :
    HasTPrivateScheme (Fin n) t k c β :=
  h.comap ((Fin.castLEEmb hn).trans (Fintype.equivFin ι).symm.toEmbedding)

theorem HasScheme.fin_of_le_card {ι β : Type} [Fintype ι] [Nonempty β] {n k c : ℕ}
    (h : HasScheme ι k c β) (hn : n ≤ Fintype.card ι) : HasScheme (Fin n) k c β :=
  HasTPrivateScheme.fin_of_le_card h hn

theorem HasTPrivateScheme.card_le_of_le {ι : Type} [Fintype ι] {t k c : ℕ}
    (h : HasTPrivateScheme ι t k c) (hkt : k ≤ t) : Fintype.card ι ≤ c := by
  obtain ⟨S, R, Q, A, _, _, _, P, hcorrect, hprivate, hk, hcomm⟩ := hasTPrivateScheme_iff.mp h
  exact (P.card_le_communication_of_card_le hcorrect hprivate (hk.trans_le hkt)).trans hcomm

end Cslib.Crypto.Protocols.PIR
