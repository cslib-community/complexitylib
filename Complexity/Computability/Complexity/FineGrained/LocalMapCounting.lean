/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.CountingCSP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration

/-!
# Preimage counting and self-reduction for constant-locality Boolean maps

In [OpenAI2026ETH] (`7ef5c0cc`, Appendix C.2, p. 52):

> **C.2. Inverting Boolean maps with constant output locality.** Fix a constant $d$. Consider a
> Boolean map $G : \{0, 1\}^n \to \{0, 1\}^m$ whose $i$th output bit has the form
> $$G(\vec{x})_i = g_i(\vec{x}|_{S_i}), \qquad S_i \subseteq [n], \qquad |S_i| \leqslant d.$$
> The input description of $G$ lists the sets $S_i$ and the truth tables of the Boolean functions
> $g_i$. Thus each output inspects only constantly many input bits, although the sets $S_i$ may
> overlap arbitrarily. Given a target $\vec{b} \in \{0, 1\}^m$, inversion asks for any $\vec{x}$
> with $G(\vec{x}) = \vec{b}$.
>
> **Corollary C.2.** For every fixed $d$ and $n \geqslant 20$, the number $|G^{-1}(\vec{b})|$ can be
> computed exactly, and a preimage can be found whenever one exists, in deterministic time
> $$(n + m)^{O_d(1)} 2^{O_d(\rho(n))}$$
> and space $(n + m)^{O_d(1)}$.

## Notation mapping and deliberate differences from the source

* Locality bound $d \mapsto k$.
* Scope $S_i \mapsto$ `LocalOutput.scope`: an ordered `List ℕ` of variable indices `< n` of length
  at most `k` in which repeated variable indices are allowed (whereas the source's $S_i \subseteq
  [n]$ is a subset).
* Truth table of $g_i \mapsto$ `LocalOutput.accepts`: the explicit list of accepted local bit
  patterns on `scope`.
* Subexponential exponent $\rho(n) \mapsto$ `interpolationScale n`, which on `main` is
  $n (\log \log (n + 16))^2 / \sqrt{\log (n + 16)}$ (the paper's $\rho(n)$ shifted by $16$).
  Because Corollary C.2 states its time bound with $2^{O_d(\rho(n))}$, the Lean bound matches
  Corollary C.2's stated bound directly; only the sharper Theorem 1.1 / Appendix D exponent used
  inside Corollary C.2's proof is out of scope here.
* Polynomial overhead $(n + m)^{O_d(1)} \mapsto (L + 1)^e$, where $L =
  (\mathrm{encLocalMapQuery}\,(G, b)).\mathrm{length}$ is the framed binary encoding length of the
  query. Since $n$ is encoded in unary and each of the $m$ output coordinates is framed, $L \ge n$
  and $L \ge m$ (while redundant or wrong-length patterns in $G$ can make $L$ larger than
  $\mathrm{poly}(n + m)$).
* The threshold $n \geqslant 20$ is absorbed into the multiplicative and additive constants of the
  machine bounds, so the Lean theorems hold for all $n : \mathbb{N}$.
* Decision (`decidableInSubexpTime_localMapHasPreimage`) is proved as an extra corollary not stated
  in Corollary C.2.

## Main definitions

* `Cslib.Complexity.LocalOutput`, `Cslib.Complexity.LocalMap`: explicit representations of local
  output coordinates and constant-locality Boolean maps $\{0, 1\}^n \to \{0, 1\}^m$.
* `Cslib.Complexity.LocalMap.eval`, `Cslib.Complexity.LocalMap.evalBits`: evaluation of a local map
  on variable assignments $\mathbb{N} \to \mathrm{Bool}$ and on $n$-bit strings `List Bool`.
* `Cslib.Complexity.LocalMap.preimageCount`: the number of preimages of a target output in
  $\{0, 1\}^n$.
* `Cslib.Complexity.LocalMap.cspSem`, `Cslib.Complexity.LocalMap.toCSP`,
  `Cslib.Complexity.LocalMap.toDeclaredCNF`, `Cslib.Complexity.LocalMap.toKSAT`: compilation of a
  local map preimage equation $G(x) = b$ into a Boolean `CSP` and a declared-variable `CNF`.
* `Cslib.Complexity.LocalMapHasPreimage`: the decision problem of local map inversion.
* `Cslib.Complexity.LocalMap.findPreimage`: variable-by-variable self-reduction using a declared
  CNF counter.

## Main results

* `Cslib.Complexity.LocalMap.eval_toCSP`,
  `Cslib.Complexity.LocalMap.preimageCount_eq_modelCountOn_toCSP`,
  `Cslib.Complexity.LocalMap.modelCountOn_toDeclaredCNF`: satisfying assignments of `G.toCSP target`
  and `LocalMap.toDeclaredCNF k (G, target)` on `Finset.range G.numVars` match preimages of `target`
  under `G`.
* `Cslib.Complexity.CountingNativeEndpoint.exists_localMapPreimageCounter`: exact subexponential
  preimage counting in polynomial space for every fixed locality `k`.
* `Cslib.Complexity.CountingNativeEndpoint.decidableInSubexpTime_localMapHasPreimage`:
  subexponential-time preimage existence for every fixed locality `k`.
* `Cslib.Complexity.CountingNativeEndpoint.exists_localMapPreimageFinder`: subexponential
  preimage finding in polynomial space via self-reduction for every fixed locality `k`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2,
  p. 52 (via Section 6.4, Proposition 6.4, pp. 43–44).
* [O. Goldreich, *Foundations of Cryptography, Volume 1: Basic Tools*][Goldreich2001]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Logic.PL.CNF Turing.MultiTapeTM SubexponentialSAT

/-! ## Local outputs and constant-locality Boolean maps -/

/-- A single output coordinate of a local Boolean map: an ordered list `scope` of input variable
indices and the list `accepts` of local bit patterns on `scope` for which the output bit is
`true`. -/
abbrev LocalOutput : Type := List ℕ × List (List Bool)

/-- A Boolean map $G : \{0, 1\}^n \to \{0, 1\}^m$ represented by its number of declared input
variables `numVars = n` and its list of `m` local output coordinates. -/
abbrev LocalMap : Type := ℕ × List LocalOutput

/-- Framed encoding of a single local output coordinate. -/
abbrev encLocalOutput : LocalOutput ↪ List Bool :=
  encPair (encList encNat) (encList (encList encBool))

/-- Framed encoding of a local map, with the declared variable count in unary and the output
coordinates in a framed list. -/
abbrev encLocalMap : LocalMap ↪ List Bool :=
  encPair encUnary (encList encLocalOutput)

/-- Framed encoding of a local map inversion / preimage query `(G, target)`. -/
abbrev encLocalMapQuery : LocalMap × List Bool ↪ List Bool :=
  encPair encLocalMap encBits

namespace LocalOutput

/-- The input variable indices inspected by a local output coordinate. -/
abbrev scope (c : LocalOutput) : List ℕ := c.1

/-- The local bit patterns accepted by a local output coordinate. -/
abbrev accepts (c : LocalOutput) : List (List Bool) := c.2

/-- Evaluate a local output coordinate on a local bit pattern `α`. -/
def evalLocal (c : LocalOutput) (α : List Bool) : Bool :=
  c.2.contains α

/-- Evaluate a local output coordinate under a global variable assignment `σ : ℕ → Bool`. -/
def eval (c : LocalOutput) (σ : ℕ → Bool) : Bool :=
  c.evalLocal (c.1.map σ)

/-- Construct a `LocalOutput` on `scope` from any Boolean predicate `f : List Bool → Bool` by
tabulating the accepted patterns in `BitString.enumList scope.length`. -/
def ofFn (scope : List ℕ) (f : List Bool → Bool) : LocalOutput :=
  (scope, (BitString.enumList scope.length).filter f)

/-- Evaluating `ofFn scope f` under `σ` agrees with `f (scope.map σ)`. -/
@[simp]
theorem eval_ofFn (scope : List ℕ) (f : List Bool → Bool) (σ : ℕ → Bool) :
    (ofFn scope f).eval σ = f (scope.map σ) := by
  unfold ofFn eval evalLocal
  dsimp only
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_filter, BitString.mem_enumList]
  exact ⟨And.right, fun hf => ⟨List.length_map σ, hf⟩⟩

/-- Validity of a local output coordinate for locality `k` and `N` declared input variables:
its scope has length at most `k` and every variable index lies in `< N`. -/
def Valid (k N : ℕ) (c : LocalOutput) : Bool :=
  decide (c.1.length ≤ k) && c.1.all (fun v => decide (v < N))

/-- Characterization of `LocalOutput.Valid k N c = true`. -/
theorem valid_eq_true_iff {k N : ℕ} {c : LocalOutput} :
    c.Valid k N = true ↔ c.1.length ≤ k ∧ ∀ v ∈ c.1, v < N := by
  simp [Valid]

end LocalOutput

namespace LocalMap

/-- Framed encoding of a CSP relation `(accepts, targetBit)` for local map inversion. -/
abbrev encCSPRel : (List (List Bool) × Bool) ↪ List Bool :=
  encPair (encList (encList encBool)) encBool

/-- Number of declared input variables $n$ of $G : \{0, 1\}^n \to \{0, 1\}^m$. -/
abbrev numVars (G : LocalMap) : ℕ := G.1

/-- List of local output coordinates of $G$. -/
abbrev outputs (G : LocalMap) : List LocalOutput := G.2

/-- Number of output bits $m$ of $G : \{0, 1\}^n \to \{0, 1\}^m$. -/
def numOutputs (G : LocalMap) : ℕ := G.2.length

/-- Evaluate a local map under an assignment `σ : ℕ → Bool`. -/
def eval (G : LocalMap) (σ : ℕ → Bool) : List Bool :=
  G.2.map fun c => c.eval σ

/-- The output list of `G.eval σ` has length `G.numOutputs`. -/
@[simp]
theorem length_eval (G : LocalMap) (σ : ℕ → Bool) :
    (G.eval σ).length = G.numOutputs := by
  simp [eval, numOutputs]

/-- Evaluate a local map on a bitstring `x : List Bool` (reading `false` past `x.length`). -/
def evalBits (G : LocalMap) (x : List Bool) : List Bool :=
  G.eval (fun v => x.getD v false)

/-- The output list of `G.evalBits x` has length `G.numOutputs`. -/
@[simp]
theorem length_evalBits (G : LocalMap) (x : List Bool) :
    (G.evalBits x).length = G.numOutputs :=
  G.length_eval _

/-- Validity of a local map for locality bound `k`: every output coordinate has scope length `≤ k`
and only inspects input variables `< G.numVars`. -/
def Valid (k : ℕ) (G : LocalMap) : Bool :=
  G.2.all (LocalOutput.Valid k G.1)

/-- Characterization of `LocalMap.Valid k G = true`. -/
theorem valid_eq_true_iff {k : ℕ} {G : LocalMap} :
    G.Valid k = true ↔ ∀ c ∈ G.2, c.1.length ≤ k ∧ ∀ v ∈ c.1, v < G.1 := by
  simp [Valid, LocalOutput.valid_eq_true_iff]

/-- Evaluation of a valid local map depends only on variable values below `G.numVars`. -/
theorem eval_congr {k : ℕ} {G : LocalMap} (hG : G.Valid k = true) {σ τ : ℕ → Bool}
    (h : ∀ v < G.numVars, σ v = τ v) : G.eval σ = G.eval τ := by
  rw [valid_eq_true_iff] at hG
  simp only [eval, List.map_inj_left]
  intro c hc
  simp only [LocalOutput.eval]
  congr 1
  exact List.map_congr_left fun v hv => h v ((hG c hc).2 v hv)

/-- The number of preimages of `target` under `G` in $\{0, 1\}^{G.\mathrm{numVars}}$. -/
def preimageCount (G : LocalMap) (target : List Bool) : ℕ :=
  (Finset.univ.filter fun σ : Finset.range G.numVars → Bool =>
    G.eval (fun v => if h : v ∈ Finset.range G.numVars then σ ⟨v, h⟩ else false) = target).card

/-- `preimageCount` is the cardinality of preimages in `Fin G.numVars → Bool`. -/
theorem preimageCount_eq_card_fin (G : LocalMap) (target : List Bool) :
    G.preimageCount target =
      (Finset.univ.filter fun σ : Fin G.numVars → Bool =>
        G.eval (fun v => if h : v < G.numVars then σ ⟨v, h⟩ else false) = target).card := by
  refine Finset.card_bij
    (fun σ _ v => σ ⟨v.1, Finset.mem_range.mpr v.2⟩)
    (fun σ hσ => ?_)
    (fun σ₁ _ σ₂ _ h => ?_)
    (fun τ hτ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    convert hσ using 2
    funext v
    by_cases hv : v < G.numVars <;> simp [hv]
  · funext ⟨v, hv⟩
    exact congrFun h ⟨v, Finset.mem_range.mp hv⟩
  · refine ⟨fun v => τ ⟨v.1, Finset.mem_range.mp v.2⟩, ?_, funext fun ⟨v, hv⟩ => rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    convert hτ using 2
    funext v
    by_cases hv : v < G.numVars <;> simp [hv]

/-- When `target.length ≠ G.numOutputs`, `G.preimageCount target = 0`. -/
theorem preimageCount_eq_zero_of_length_ne {G : LocalMap} {target : List Bool}
    (hne : target.length ≠ G.numOutputs) : G.preimageCount target = 0 := by
  rw [preimageCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro σ _ heq
  apply hne
  rw [← heq, length_eval]

/-- CSP relation semantics for local map preimage constraints `(accepts, targetBit)`. -/
def cspSem (rel : List (List Bool) × Bool) (w : List Bool) : Bool :=
  rel.1.contains w == rel.2

/-- Express the local map preimage equation `G(x) = target` as a Boolean CSP over relation
alphabet `List (List Bool) × Bool`, emitting one constraint `((c.accepts, target_i), c.scope)` per
output coordinate. -/
def toCSP (G : LocalMap) (target : List Bool) : CSP (List (List Bool) × Bool) ℕ :=
  (G.2.zip target).map fun p => ((p.1.2, p.2), p.1.1)

private theorem eval_map_zip_toCSP (cs : List LocalOutput) (bs : List Bool)
    (hlen : bs.length = cs.length) (σ : ℕ → Bool) :
    CSP.eval cspSem σ ((cs.zip bs).map fun p => ((p.1.2, p.2), p.1.1)) =
      decide (cs.map (fun c => c.eval σ) = bs) := by
  induction cs generalizing bs with
  | nil =>
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hbs
    rfl
  | cons c cs ih =>
    rcases bs with _ | ⟨b, bs⟩
    · simp at hlen
    · simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      change (Constraint.eval cspSem σ ((c.2, b), c.1) &&
          CSP.eval cspSem σ ((cs.zip bs).map fun p => ((p.1.2, p.2), p.1.1))) =
        decide (c.eval σ :: cs.map (fun c => c.eval σ) = b :: bs)
      rw [ih bs hlen]
      change ((c.eval σ == b) && decide (cs.map (fun c => c.eval σ) = bs)) =
        decide (c.eval σ :: cs.map (fun c => c.eval σ) = b :: bs)
      by_cases h1 : c.eval σ = b <;> by_cases h2 : cs.map (fun c => c.eval σ) = bs <;>
        simp [h1, h2]

/-- When `target.length = G.numOutputs`, `(G.toCSP target).eval cspSem σ` holds if and only if
`G.eval σ = target`. -/
theorem eval_toCSP {G : LocalMap} {target : List Bool} (hlen : target.length = G.numOutputs)
    (σ : ℕ → Bool) :
    (G.toCSP target).eval cspSem σ = decide (G.eval σ = target) :=
  eval_map_zip_toCSP G.2 target hlen σ

/-- When `target.length = G.numOutputs`, `G.evalBits x = target` holds if and only if the
assignment `fun v => x.getD v false` satisfies `G.toCSP target`. -/
theorem evalBits_eq_iff_eval_toCSP {G : LocalMap} {target : List Bool}
    (hlen : target.length = G.numOutputs) (x : List Bool) :
    G.evalBits x = target ↔
      (G.toCSP target).eval cspSem (fun v => x.getD v false) = true := by
  rw [eval_toCSP hlen, decide_eq_true_eq, evalBits]

/-- **Exact-multiplicity CSP preimage preservation:** When `target.length = G.numOutputs`,
`G.preimageCount target` equals the declared-variable CSP model count of `G.toCSP target` on
`Finset.range G.numVars`. -/
theorem preimageCount_eq_modelCountOn_toCSP {G : LocalMap} {target : List Bool}
    (hlen : target.length = G.numOutputs) :
    G.preimageCount target =
      (G.toCSP target).modelCountOn cspSem (Finset.range G.numVars) := by
  simp only [preimageCount, CSP.modelCountOn, eval_toCSP hlen, decide_eq_true_eq]
  rfl

/-- For any `k`-valid local map `G`, `G.toCSP target` satisfies
`CSP.validDeclaredCSP k G.numVars`. -/
theorem validDeclaredCSP_toCSP {k : ℕ} {G : LocalMap} (hG : G.Valid k = true)
    (target : List Bool) :
    CSP.validDeclaredCSP k G.numVars (G.toCSP target) = true := by
  rw [valid_eq_true_iff] at hG
  rw [CSP.validDeclaredCSP_eq_true_iff]
  refine ⟨?_, ?_⟩
  · intro c hc
    simp only [toCSP, List.mem_map] at hc
    rcases hc with ⟨⟨out, b⟩, hmem, rfl⟩
    exact (hG out (List.of_mem_zip hmem).1).1
  · intro v hv
    simp only [CSP.vars, toCSP, List.mem_toFinset, List.mem_flatMap, List.mem_map] at hv
    rcases hv with ⟨c, ⟨⟨out, b⟩, hmem, rfl⟩, hv_in⟩
    exact Finset.mem_range.mpr ((hG out (List.of_mem_zip hmem).1).2 v hv_in)

/-- A valid `k`-local map has a positive preimage count for `target` if and only if there exists
an `n`-bit input `x : List Bool` with `x.length = G.numVars` and `G.evalBits x = target`. -/
theorem preimageCount_pos_iff {k : ℕ} {G : LocalMap} (hG : G.Valid k = true)
    (target : List Bool) :
    0 < G.preimageCount target ↔
      ∃ x : List Bool, x.length = G.numVars ∧ G.evalBits x = target := by
  rw [preimageCount, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨σ, -, hσ⟩
    let ext (v : ℕ) : Bool := if h : v ∈ Finset.range G.numVars then σ ⟨v, h⟩ else false
    refine ⟨(List.range G.numVars).map ext, by simp, ?_⟩
    rw [evalBits, ← hσ]
    refine eval_congr hG fun v hv => ?_
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv,
      Option.map_some, Option.getD_some]
    rfl
  · rintro ⟨x, hxlen, hx⟩
    refine ⟨fun v => x.getD v.1 false, Finset.mem_univ _, ?_⟩
    rw [← hx, evalBits]
    refine eval_congr hG fun v hv => ?_
    have hmem : v ∈ Finset.range G.numVars := Finset.mem_range.mpr hv
    simp [hmem]

end LocalMap

/-! ## Polynomial-time computability of local map operations -/

section PolyTime

open ComputableInPolyTime

private theorem computableInPolyTime_zip {α β : Type}
    (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List β => p.1.zip p.2)
      (encPair (encList encA) (encList encB)) (encList (encPair encA encB)) := by
  rcases isEmpty_or_nonempty α with h | h
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.1 with
      | nil => rfl
      | cons a _ => exact isEmptyElim a
    rw [heq]
    exact const []
  rcases isEmpty_or_nonempty β with h' | h'
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.2 with
      | nil => simp
      | cons b _ => exact isEmptyElim b
    rw [heq]
    exact const []
  obtain ⟨a⟩ := h
  obtain ⟨b⟩ := h'
  have heq (p : List α × List β) : p.1.zip p.2 =
      (List.range (p.1.length - (p.1.length - p.2.length))).map
        (fun i => (p.1.getD i a, p.2.getD i b)) := by
    have hmin : p.1.length - (p.1.length - p.2.length) = min p.1.length p.2.length := by omega
    rw [hmin]
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have hleft : i < p.1.length := (Nat.lt_min.mp (by simpa only [List.length_zip] using hi)).1
    have hright : i < p.2.length := (Nat.lt_min.mp (by simpa only [List.length_zip] using hi)).2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hleft,
      List.getElem?_eq_getElem hright, Option.getD_some]
  simp_rw [heq]
  fun_prop

private theorem list_contains_eq_any {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    l.contains x = l.any (fun y => y == x) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true]
  simp [@eq_comm _ _ x]

/-- `LocalOutput.evalLocal` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_localOutput_evalLocal :
    ComputableInPolyTime (fun p : LocalOutput × List Bool => p.1.evalLocal p.2)
      (encPair encLocalOutput (encList encBool)) encBool := by
  have h : ComputableInPolyTime
      (fun p : LocalOutput × List Bool => p.1.2.any fun β => β == p.2)
      (encPair encLocalOutput (encList encBool)) encBool := by
    unfold encLocalOutput
    fun_prop
  exact h.of_enc_eq fun p => by simp only [LocalOutput.evalLocal, list_contains_eq_any]

/-- `LocalMap.cspSem` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_cspSem :
    ComputableInPolyTime (fun p : (List (List Bool) × Bool) × List Bool =>
      LocalMap.cspSem p.1 p.2)
      (encPair LocalMap.encCSPRel encBits) encBool := by
  have hbits : ComputableInPolyTime
      (fun p : (List (List Bool) × Bool) × List Bool => p.2)
      (encPair LocalMap.encCSPRel encBits) (encList encBool) :=
    (bits_encList_polyTime encBool).1.comp (snd LocalMap.encCSPRel encBits)
  have hcontains : ComputableInPolyTime
      (fun p : (List (List Bool) × Bool) × List Bool => p.1.1.any fun β => β == p.2)
      (encPair LocalMap.encCSPRel encBits) encBool := by
    apply anyWithInput (by unfold LocalMap.encCSPRel; fun_prop)
    exact beq (snd _ _) (hbits.comp (fst _ _))
  have hrel : ComputableInPolyTime
      (fun p : (List (List Bool) × Bool) × List Bool =>
        (p.1.1.any fun β => β == p.2) == p.1.2)
      (encPair LocalMap.encCSPRel encBits) encBool :=
    beq hcontains ((snd (encList (encList encBool)) encBool).comp (fst LocalMap.encCSPRel encBits))
  exact hrel.of_enc_eq fun p => by simp only [LocalMap.cspSem, list_contains_eq_any]

/-- `LocalOutput.Valid k` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_localOutput_valid (k : ℕ) :
    ComputableInPolyTime (fun p : ℕ × LocalOutput => p.2.Valid k p.1)
      (encPair encUnary encLocalOutput) encBool := by
  have hN : ComputableInPolyTime (fun p : ℕ × LocalOutput => p.1)
      (encPair encUnary encLocalOutput) encNat :=
    unary_to_binary.comp (fst encUnary encLocalOutput)
  have hlt : ComputableInPolyTime
      (fun q : (ℕ × LocalOutput) × ℕ => decide (q.2 < q.1.1))
      (encPair (encPair encUnary encLocalOutput) encNat) encBool :=
    binary_lt.comp ((snd _ _).prod (hN.comp (fst _ _)))
  have hall : ComputableInPolyTime
      (fun p : ℕ × LocalOutput => p.2.1.all fun v => decide (v < p.1))
      (encPair encUnary encLocalOutput) encBool :=
    allWithInput (by unfold encLocalOutput; fun_prop) hlt
  unfold LocalOutput.Valid encLocalOutput
  fun_prop

/-- `LocalMap.Valid k` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_localMap_valid (k : ℕ) :
    ComputableInPolyTime (LocalMap.Valid k) encLocalMap encBool := by
  unfold LocalMap.Valid encLocalMap
  fun_prop

/-- `LocalMap.toCSP` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_localMap_toCSP :
    ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.toCSP q.2)
      encLocalMapQuery (encCSP LocalMap.encCSPRel encNat) := by
  have hout : ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.2)
      encLocalMapQuery (encList encLocalOutput) :=
    (snd encUnary (encList encLocalOutput)).comp (fst encLocalMap encBits)
  have hbits : ComputableInPolyTime (fun q : LocalMap × List Bool => q.2)
      encLocalMapQuery (encList encBool) :=
    (bits_encList_polyTime encBool).1.comp (snd encLocalMap encBits)
  have hzip : ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.2.zip q.2)
      encLocalMapQuery (encList (encPair encLocalOutput encBool)) :=
    (computableInPolyTime_zip encLocalOutput encBool).comp (hout.prod hbits)
  have hentry : ComputableInPolyTime
      (fun p : LocalOutput × Bool => ((p.1.2, p.2), p.1.1))
      (encPair encLocalOutput encBool) (encConstraint LocalMap.encCSPRel encNat) := by
    unfold encLocalOutput encConstraint LocalMap.encCSPRel
    fun_prop
  exact (map hentry).comp hzip

/-- `LocalMap.evalBits` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_localMap_evalBits :
    ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.evalBits q.2)
      encLocalMapQuery (encList encBool) := by
  have hget : ComputableInPolyTime
      (fun p : (LocalMap × List Bool) × ℕ => p.1.2.getD p.2 false)
      (encPair encLocalMapQuery encNat) encBool :=
    listGetD_binary false ((snd encLocalMap encBits).comp (fst _ _)) (snd _ _)
  have hscope : ComputableInPolyTime
      (fun p : (LocalMap × List Bool) × LocalOutput =>
        p.2.1.map fun v => p.1.2.getD v false)
      (encPair encLocalMapQuery encLocalOutput) (encList encBool) := by
    apply mapWithInput (by unfold encLocalOutput; fun_prop)
    exact hget.comp (((fst _ _).comp (fst _ _)).prod (snd _ _))
  have hcoord : ComputableInPolyTime
      (fun p : (LocalMap × List Bool) × LocalOutput =>
        p.2.evalLocal (p.2.1.map fun v => p.1.2.getD v false))
      (encPair encLocalMapQuery encLocalOutput) encBool :=
    computableInPolyTime_localOutput_evalLocal.comp ((snd _ _).prod hscope)
  change ComputableInPolyTime
    (fun q : LocalMap × List Bool =>
      q.1.2.map fun c => c.evalLocal (c.1.map fun v => q.2.getD v false))
    encLocalMapQuery (encList encBool)
  exact mapWithInput (by unfold encLocalMapQuery encLocalMap; fun_prop) hcoord

end PolyTime

/-! ## Section 4: Preimage counting and decision endpoints via `CSP.toCNFBounded` -/

/-- The decision problem of whether a `k`-local map query `(G, target)` is `k`-valid and has at
least one preimage in `{0, 1}^{G.numVars}`. -/
def LocalMapHasPreimage (k : ℕ) : Set (LocalMap × List Bool) :=
  {q | q.1.Valid k = true ∧ 0 < q.1.preimageCount q.2}

namespace LocalMap

/-- Guard checking that `G` is `k`-valid and `target` has length `G.numOutputs`. -/
def ValidQuery (k : ℕ) (q : LocalMap × List Bool) : Bool :=
  q.1.Valid k && decide (q.2.length = q.1.numOutputs)

open ComputableInPolyTime in
/-- `LocalMap.ValidQuery k` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_validQuery (k : ℕ) :
    ComputableInPolyTime (ValidQuery k) encLocalMapQuery encBool := by
  have hval : ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.Valid k)
      encLocalMapQuery encBool :=
    (computableInPolyTime_localMap_valid k).comp (fst encLocalMap encBits)
  have hout : ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.2)
      encLocalMapQuery (encList encLocalOutput) :=
    (snd encUnary (encList encLocalOutput)).comp (fst encLocalMap encBits)
  have hlen : ComputableInPolyTime
      (fun q : LocalMap × List Bool => decide (q.2.length = q.1.numOutputs))
      encLocalMapQuery encBool :=
    decide_eq' (length_bits.comp (snd encLocalMap encBits))
      ((length_list encLocalOutput).comp hout)
  exact bool_and' hval hlen

/-- Convert a local map query `(G, target)` into a declared-variable CNF instance `(N, φ)` for
width `k` by compiling `G.toCSP target` via `CSP.toCNFBounded k LocalMap.cspSem` when
`LocalMap.ValidQuery k q` holds, and emitting `(G.numVars, [[]])` otherwise. -/
def toDeclaredCNF (k : ℕ) (q : LocalMap × List Bool) : ℕ × CNF ℕ :=
  (q.1.numVars,
    if ValidQuery k q then
      (q.1.toCSP q.2).toCNFBounded k LocalMap.cspSem
    else
      [[]])

/-- The declared variable count of `LocalMap.toDeclaredCNF k q` is `q.1.numVars`. -/
@[simp]
theorem toDeclaredCNF_fst (k : ℕ) (q : LocalMap × List Bool) :
    (toDeclaredCNF k q).1 = q.1.numVars := rfl

/-- For `k ≤ k'`, `LocalMap.toDeclaredCNF k q` always produces a valid declared `k'`-CNF input. -/
theorem validDeclaredInput_toDeclaredCNF {k k' : ℕ} (hk : k ≤ k') (q : LocalMap × List Bool) :
    validDeclaredInput k' (toDeclaredCNF k q).1 (toDeclaredCNF k q).2 = true := by
  unfold toDeclaredCNF ValidQuery
  dsimp only
  split_ifs with hq
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    have h := CSP.validDeclaredInput_toCNFBounded LocalMap.cspSem
      (q.1.validDeclaredCSP_toCSP hq.1 q.2)
    rw [validDeclaredInput_eq_true_iff] at h ⊢
    exact ⟨fun cl hcl => (h.1 cl hcl).trans hk, h.2⟩
  · rw [validDeclaredInput_eq_true_iff]
    refine ⟨?_, ?_⟩
    · intro cl hcl
      simp only [List.mem_singleton] at hcl
      simp [hcl]
    · simp [CNF.vars]

/-- Evaluating the CNF produced by `LocalMap.toDeclaredCNF k q` under `σ` tests whether `q.1` is
`k`-valid and `q.1.eval σ = q.2`. -/
theorem eval_toDeclaredCNF (k : ℕ) (q : LocalMap × List Bool) (σ : ℕ → Bool) :
    (toDeclaredCNF k q).2.eval σ = (q.1.Valid k && decide (q.1.eval σ = q.2)) := by
  unfold toDeclaredCNF ValidQuery
  dsimp only
  by_cases hG : q.1.Valid k = true
  · by_cases hlen : q.2.length = q.1.numOutputs
    · have hwidth : ∀ c ∈ q.1.toCSP q.2, c.2.length ≤ k :=
        (CSP.validDeclaredCSP_eq_true_iff.mp (q.1.validDeclaredCSP_toCSP hG q.2)).1
      simp only [hG, hlen, decide_true, Bool.and_self, ↓reduceIte,
        CSP.toCNFBounded_eq_toCNF hwidth, CSP.eval_toCNF, q.1.eval_toCSP hlen, Bool.true_and]
    · have hne : q.1.eval σ ≠ q.2 := by
        intro heq
        apply hlen
        rw [← heq, q.1.length_eval]
      simp [hG, hlen, hne, CNF.eval, Clause.eval]
  · simp [hG, CNF.eval, Clause.eval]

/-- The declared-variable model count of `LocalMap.toDeclaredCNF k q` equals `q.1.preimageCount q.2`
when `q.1` is `k`-valid, and `0` otherwise. -/
theorem modelCountOn_toDeclaredCNF (k : ℕ) (q : LocalMap × List Bool) :
    (toDeclaredCNF k q).2.modelCountOn (Finset.range (toDeclaredCNF k q).1) =
      if q.1.Valid k then q.1.preimageCount q.2 else 0 := by
  unfold CNF.modelCountOn LocalMap.preimageCount
  dsimp only [toDeclaredCNF_fst]
  split_ifs with hG
  · simp only [eval_toDeclaredCNF, hG, Bool.true_and, decide_eq_true_eq]
    rfl
  · simp only [eval_toDeclaredCNF, hG, Bool.false_and, Bool.false_eq_true, Finset.filter_false,
      Finset.card_empty]

open ComputableInPolyTime in
/-- `LocalMap.toDeclaredCNF k` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toDeclaredCNF (k : ℕ) :
    ComputableInPolyTime (toDeclaredCNF k) encLocalMapQuery (encPair encUnary encCNF) := by
  have hn : ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.numVars)
      encLocalMapQuery encUnary :=
    (fst encUnary (encList encLocalOutput)).comp (fst encLocalMap encBits)
  have hcompile : ComputableInPolyTime
      (fun q : LocalMap × List Bool => (q.1.toCSP q.2).toCNFBounded k LocalMap.cspSem)
      encLocalMapQuery encCNF :=
    (CSP.computableInPolyTime_toCNFBounded LocalMap.encCSPRel encNat k LocalMap.cspSem
      computableInPolyTime_cspSem).comp computableInPolyTime_localMap_toCSP
  have hcnf : ComputableInPolyTime
      (fun q : LocalMap × List Bool =>
        if ValidQuery k q then (q.1.toCSP q.2).toCNFBounded k LocalMap.cspSem else [[]])
      encLocalMapQuery encCNF :=
    (computableInPolyTime_validQuery k).ite hcompile (const [[]])
  exact hn.prod hcnf

/-- Polynomial-time reduction from `LocalMapHasPreimage k` to `KSAT k`. -/
def toKSAT (k : ℕ) (q : LocalMap × List Bool) : CNF ℕ :=
  (toDeclaredCNF k q).2

open ComputableInPolyTime in
/-- `LocalMap.toKSAT k` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toKSAT (k : ℕ) :
    ComputableInPolyTime (toKSAT k) encLocalMapQuery encCNF :=
  (snd encUnary encCNF).comp (computableInPolyTime_toDeclaredCNF k)

/-- The number of occurring variables in `LocalMap.toKSAT k q` is at most `q.1.numVars`. -/
theorem numVars_toKSAT_le (k : ℕ) (q : LocalMap × List Bool) :
    (toKSAT k q).numVars ≤ q.1.numVars := by
  have hsub :=
    (validDeclaredInput_eq_true_iff.mp (validDeclaredInput_toDeclaredCNF (le_rfl : k ≤ k) q)).2
  simpa only [toKSAT, toDeclaredCNF_fst, CNF.numVars, Finset.card_range] using
    Finset.card_le_card hsub

/-- `LocalMap.toKSAT k` is a many-one reduction from `LocalMapHasPreimage k` to `KSAT k`. -/
theorem mem_localMapHasPreimage_iff_toKSAT_mem_KSAT (k : ℕ) (q : LocalMap × List Bool) :
    q ∈ LocalMapHasPreimage k ↔ toKSAT k q ∈ KSAT k := by
  have hvalid :=
    validDeclaredInput_eq_true_iff.mp (validDeclaredInput_toDeclaredCNF (le_rfl : k ≤ k) q)
  have hmc := CNF.modelCountOn_eq_mul_modelCount (toDeclaredCNF k q).2
    (Finset.range (toDeclaredCNF k q).1) hvalid.2
  rw [modelCountOn_toDeclaredCNF] at hmc
  simp only [LocalMapHasPreimage, KSAT, toKSAT, Set.mem_ofPred_eq, ← CNF.modelCount_pos_iff]
  by_cases hG : q.1.Valid k = true
  · simp only [hG, ↓reduceIte, true_and] at hmc ⊢
    rw [hmc]
    exact ⟨fun h => ⟨hvalid.1, pos_of_mul_pos_right h (Nat.zero_le _)⟩,
      fun h => Nat.mul_pos (Nat.two_pow_pos _) h.2⟩
  · simp only [hG, Bool.false_eq_true, ↓reduceIte, false_and, false_iff] at hmc ⊢
    rintro ⟨-, hpos⟩
    have hmul_pos : 0 < 2 ^ ((Finset.range (toDeclaredCNF k q).1).card -
        (toDeclaredCNF k q).2.numVars) * (toDeclaredCNF k q).2.modelCount :=
      Nat.mul_pos (Nat.two_pow_pos _) hpos
    omega

end LocalMap

namespace CountingNativeEndpoint

open SubexponentialSAT

private theorem computableInO_of_declared_localMap_bounds {β : Type*} {encOut : β ↪ List Bool}
    {f : LocalMap × List Bool → β} {T S : LocalMap × List Bool → ℕ} {A c e a b : ℕ}
    (hf : ComputableInO f encLocalMapQuery encOut T S)
    (hT : ∀ q : LocalMap × List Bool,
      (T q : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) *
        (((encLocalMapQuery q).length : ℝ) + 1) ^ e) + c)
    (hS : ∀ q : LocalMap × List Bool, S q ≤ a * ((encLocalMapQuery q).length + 1) ^ b) :
    ComputableInO f encLocalMapQuery encOut
      (fun q => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars)⌉₊ *
        ((encLocalMapQuery q).length + 1) ^ e)
      (fun q => ((encLocalMapQuery q).length + 1) ^ b) := by
  refine hf.mono (c + c + a + 1) (fun q => ?_) (fun q => ?_)
  · set Y := (encLocalMapQuery q).length + 1
    set X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars)
    set N := ⌈X⌉₊
    have hXN : X ≤ N := Nat.le_ceil X
    have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hY1 : 1 ≤ Y ^ e := Nat.one_le_pow _ _ (Nat.le_add_left 1 _)
    have hNY1 : 1 ≤ N * Y ^ e := Nat.mul_pos hN1 hY1
    have hTq : T q ≤ c * (N * Y ^ e) + c := by
      have h := hT q
      have h1 : X * (Y : ℝ) ^ e ≤ (N : ℝ) * (Y : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right hXN (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
      have : (T q : ℝ) ≤ (c * (N * Y ^ e) + c : ℕ) := by
        dsimp only [X, Y] at h2 ⊢
        push_cast at h2 ⊢
        linarith
      exact_mod_cast this
    calc T q ≤ c * (N * Y ^ e) + c := hTq
      _ ≤ c * (N * Y ^ e) + c * (N * Y ^ e) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right c hNY1) _
      _ = (c + c) * (N * Y ^ e) := by ring
      _ ≤ (c + c + a + 1) * (N * Y ^ e + 1) := Nat.mul_le_mul (by omega) (by omega)
  · exact (hS q).trans (Nat.mul_le_mul (by omega) (by omega))

/-- **Declared-form local map preimage counter (Corollary C.2):** For every fixed locality bound
`k`, one native machine computes the exact preimage count `G.preimageCount target` for every valid
`k`-local map `G` (and `0` when `G` is invalid), in time
$2^{O_k(\mathrm{interpolationScale}(n))} \cdot \mathrm{poly}(L)$ and polynomial space
$\mathrm{poly}(L)$. -/
public theorem exists_localMapPreimageCounter_declared (k : ℕ) :
    ∃ (count : LocalMap × List Bool → ℕ) (T S : LocalMap × List Bool → ℕ) (A c e a b : ℕ),
      ComputableInO count encLocalMapQuery encNat T S ∧
      (∀ q : LocalMap × List Bool,
        count q = if q.1.Valid k then q.1.preimageCount q.2 else 0) ∧
      (∀ q : LocalMap × List Bool,
        (T q : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) *
          (((encLocalMapQuery q).length : ℝ) + 1) ^ e) + c) ∧
      (∀ q : LocalMap × List Bool, S q ≤ a * ((encLocalMapQuery q).length + 1) ^ b) := by
  have hvalid : ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.Valid k)
      encLocalMapQuery encBool :=
    (computableInPolyTime_localMap_valid k).comp (ComputableInPolyTime.fst encLocalMap encBits)
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ :=
    exists_counter_of_polyTime_toDeclared k (LocalMap.computableInPolyTime_toDeclaredCNF k) hvalid
      (fun q _ => LocalMap.validDeclaredInput_toDeclaredCNF (le_rfl : k ≤ k) q)
  refine ⟨count, T, S, A, c, e, a, b, hcount, fun q => ?_, hT, hS⟩
  rw [hspec q, LocalMap.modelCountOn_toDeclaredCNF]
  split_ifs <;> rfl

/-- **Subexponential local map preimage counting (Corollary C.2):** For every fixed locality bound
`k`, one native machine computes `G.preimageCount target` for every valid `k`-local map `G` and
target `target`, within time `⌈2 ^ (A * interpolationScale G.numVars)⌉₊ * (L + 1) ^ e` and space
`(L + 1) ^ b`. -/
public theorem exists_localMapPreimageCounter (k : ℕ) :
    ∃ (count : LocalMap × List Bool → ℕ) (A e b : ℕ),
      (∀ q : LocalMap × List Bool, q.1.Valid k = true → count q = q.1.preimageCount q.2) ∧
      ComputableInO count encLocalMapQuery encNat
        (fun q => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars)⌉₊ *
          ((encLocalMapQuery q).length + 1) ^ e)
        (fun q => ((encLocalMapQuery q).length + 1) ^ b) := by
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ :=
    exists_localMapPreimageCounter_declared k
  exact ⟨count, A, e, b, fun q hG => by simp [hspec, hG],
    computableInO_of_declared_localMap_bounds hcount hT hS⟩

/-- **Subexponential-time preimage existence for constant-locality maps (Corollary C.2):**
For every fixed locality bound `k`, `LocalMapHasPreimage k` is decidable in subexponential time in
the number of input variables `G.numVars`. -/
public theorem decidableInSubexpTime_localMapHasPreimage (k : ℕ) :
    DecidableInSubexpTime (LocalMapHasPreimage k) encLocalMapQuery (fun q => q.1.numVars) :=
  DecidableInSubexpTime.of_reduction
    (LocalMap.computableInPolyTime_toKSAT k)
    (LocalMap.mem_localMapHasPreimage_iff_toKSAT_mem_KSAT k)
    (c := 1)
    (fun q => by have := LocalMap.numVars_toKSAT_le k q; omega)
    (decidableInSubexpTime_KSAT k)

end CountingNativeEndpoint

/-! ## Section 5: Prefix self-reduction and preimage finding -/

namespace LocalMap

/-- Unit clauses fixing the first `u.length` input variables `0, ..., u.length - 1` to the bits of
`u`. -/
def prefixUnits (u : List Bool) : CNF ℕ :=
  (List.range u.length).map fun j => [(j, u.getD j false)]

@[simp]
private theorem prefixUnits_nil : prefixUnits [] = [] := rfl

private theorem eval_prefixUnits (u : List Bool) (σ : ℕ → Bool) :
    (prefixUnits u).eval σ = true ↔ ∀ j < u.length, σ j = u.getD j false := by
  simp only [prefixUnits, CNF.eval_map_eq_true_iff, List.mem_range, Clause.eval_cons,
    Clause.eval_nil, Bool.or_false, Literal.eval_mk, beq_iff_eq]

private theorem eval_prefixUnits_append_singleton (u : List Bool) (b : Bool) (σ : ℕ → Bool) :
    (prefixUnits (u ++ [b])).eval σ = true ↔
      (prefixUnits u).eval σ = true ∧ σ u.length = b := by
  rw [eval_prefixUnits, eval_prefixUnits, List.length_append, List.length_singleton]
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have h1 := h j (Nat.lt_succ_of_lt hj)
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hj] using h1
    · have h2 := h u.length (Nat.lt_succ_self _)
      simpa [List.getD_eq_getElem?_getD] using h2
  · rintro ⟨hu, hb⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] using hu j hlt
    · simpa [List.getD_eq_getElem?_getD] using hb

private theorem modelCountOn_append_prefixUnits_split (φ : CNF ℕ) (u : List Bool)
    (declared : Finset ℕ) :
    (φ ++ prefixUnits u).modelCountOn declared =
      (φ ++ prefixUnits (u ++ [false])).modelCountOn declared +
        (φ ++ prefixUnits (u ++ [true])).modelCountOn declared := by
  let ext (σ : declared → Bool) (v : ℕ) : Bool := if h : v ∈ declared then σ ⟨v, h⟩ else false
  let S : Finset (declared → Bool) :=
    Finset.univ.filter fun σ => (φ ++ prefixUnits u).eval (ext σ) = true
  have hfalse : (Finset.univ.filter fun σ : declared → Bool =>
      (φ ++ prefixUnits (u ++ [false])).eval (ext σ) = true) =
      S.filter (fun σ => ¬(ext σ u.length = true)) := by
    ext σ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, CNF.eval_append,
      Bool.and_eq_true, eval_prefixUnits_append_singleton, Bool.not_eq_true, and_assoc]
  have htrue : (Finset.univ.filter fun σ : declared → Bool =>
      (φ ++ prefixUnits (u ++ [true])).eval (ext σ) = true) =
      S.filter (fun σ => ext σ u.length = true) := by
    ext σ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, CNF.eval_append,
      Bool.and_eq_true, eval_prefixUnits_append_singleton, and_assoc]
  change S.card =
    (Finset.univ.filter fun σ : declared → Bool =>
      (φ ++ prefixUnits (u ++ [false])).eval (ext σ) = true).card +
    (Finset.univ.filter fun σ : declared → Bool =>
      (φ ++ prefixUnits (u ++ [true])).eval (ext σ) = true).card
  rw [hfalse, htrue, Nat.add_comm]
  exact (Finset.card_filter_add_card_filter_not (s := S)
    (p := fun σ => ext σ u.length = true)).symm

private theorem validDeclaredInput_append_prefixUnits {k N : ℕ} {φ : CNF ℕ}
    (hφ : validDeclaredInput (max 1 k) N φ = true) {u : List Bool} (hu : u.length ≤ N) :
    validDeclaredInput (max 1 k) N (φ ++ prefixUnits u) = true := by
  rw [validDeclaredInput_eq_true_iff] at hφ ⊢
  refine ⟨fun cl hcl => ?_, fun v hv => ?_⟩
  · rcases List.mem_append.mp hcl with hcl | hcl
    · exact hφ.1 cl hcl
    · simp only [prefixUnits, List.mem_map, List.mem_range] at hcl
      obtain ⟨j, _, rfl⟩ := hcl
      exact le_max_left 1 k
  · obtain ⟨cl, hcl, pol, hl⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
    rcases List.mem_append.mp hcl with hcl | hcl
    · exact hφ.2 (List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨cl, hcl, pol, hl⟩))
    · simp only [prefixUnits, List.mem_map, List.mem_range] at hcl
      obtain ⟨j, hj, rfl⟩ := hcl
      simp only [List.mem_singleton, Prod.mk.injEq] at hl
      exact Finset.mem_range.mpr (hl.1 ▸ hj.trans_le hu)

/-- State of the prefix self-reduction loop: the fixed declared-variable CNF instance `(N, φ)`
together with the partial assignment prefix `u : List Bool` constructed so far. -/
abbrev PreimageSearchState : Type := (ℕ × CNF ℕ) × List Bool

/-- Encoding of `LocalMap.PreimageSearchState`. -/
private abbrev encPreimageSearchState : PreimageSearchState ↪ List Bool :=
  encPair (encPair encUnary encCNF) encBits

/-- Build the declared-variable CNF query testing whether `u ++ [false]` can be extended to a
satisfying assignment of `st.1.2` on `Finset.range st.1.1`. -/
def makePreimageQuery (st : PreimageSearchState) : ℕ × CNF ℕ :=
  (st.1.1, st.1.2 ++ prefixUnits (st.2 ++ [false]))

/-- One step of prefix self-reduction parameterized by a declared-variable counter `count`:
append `false` if `u ++ [false]` has at least one extension (`count (...) != 0`), and `true`
otherwise (`count (...) == 0`). -/
def preimageStepWith (count : ℕ × CNF ℕ → ℕ) (st : PreimageSearchState) : PreimageSearchState :=
  (st.1, st.2 ++ [count (makePreimageQuery st) == 0])

@[simp]
private theorem iterate_preimageStepWith_fst (count : ℕ × CNF ℕ → ℕ) (i : ℕ)
    (st : PreimageSearchState) :
    ((preimageStepWith count)^[i] st).1 = st.1 := by
  induction i generalizing st with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl

@[simp]
private theorem length_snd_iterate_preimageStepWith (count : ℕ × CNF ℕ → ℕ) (i : ℕ)
    (st : PreimageSearchState) :
    ((preimageStepWith count)^[i] st).2.length = st.2.length + i := by
  induction i generalizing st with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [preimageStepWith, List.length_append, List.length_singleton]
    omega

/-- Canonical mathematical declared-variable counter on `Finset.range p.1`. -/
def canonicalDeclaredCount (p : ℕ × CNF ℕ) : ℕ :=
  p.2.modelCountOn (Finset.range p.1)

private theorem iterate_preimageStepWith_congr {k : ℕ} {count : ℕ × CNF ℕ → ℕ}
    (hcount : ∀ p : ℕ × CNF ℕ, validDeclaredInput (max 1 k) p.1 p.2 = true →
      count p = canonicalDeclaredCount p)
    {p : ℕ × CNF ℕ} (hp : validDeclaredInput (max 1 k) p.1 p.2 = true) :
    ∀ (i : ℕ) (u : List Bool), u.length + i ≤ p.1 →
      (preimageStepWith count)^[i] (p, u) =
        (preimageStepWith canonicalDeclaredCount)^[i] (p, u)
  | 0, _, _ => rfl
  | i + 1, u, hu => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hu1 : (u ++ [false]).length ≤ p.1 := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hvalid : validDeclaredInput (max 1 k) p.1 (p.2 ++ prefixUnits (u ++ [false])) = true :=
      validDeclaredInput_append_prefixUnits hp hu1
    have hstep : preimageStepWith count (p, u) =
        preimageStepWith canonicalDeclaredCount (p, u) := by
      simp only [preimageStepWith, makePreimageQuery, hcount (p.1, _) hvalid]
    rw [hstep]
    exact iterate_preimageStepWith_congr hcount hp i _ (by
      simp only [List.length_append, List.length_singleton]
      omega)

private theorem modelCountOn_pos_preimageStepWith_canonical (p : ℕ × CNF ℕ) (u : List Bool)
    (hpos : 0 < (p.2 ++ prefixUnits u).modelCountOn (Finset.range p.1)) :
    0 < (p.2 ++ prefixUnits (preimageStepWith canonicalDeclaredCount (p, u)).2).modelCountOn
      (Finset.range p.1) := by
  have hsplit := modelCountOn_append_prefixUnits_split p.2 u (Finset.range p.1)
  simp only [preimageStepWith, makePreimageQuery, canonicalDeclaredCount]
  by_cases h0 : (p.2 ++ prefixUnits (u ++ [false])).modelCountOn (Finset.range p.1) = 0
  · simp only [h0, beq_self_eq_true]
    omega
  · have hbeq : ((p.2 ++ prefixUnits (u ++ [false])).modelCountOn (Finset.range p.1) == 0) =
        false := beq_eq_false_iff_ne.mpr h0
    simp only [hbeq]
    omega

private theorem modelCountOn_pos_iterate_preimageStepWith_canonical (p : ℕ × CNF ℕ) (i : ℕ)
    (u : List Bool) (hpos : 0 < (p.2 ++ prefixUnits u).modelCountOn (Finset.range p.1)) :
    0 < (p.2 ++ prefixUnits ((preimageStepWith canonicalDeclaredCount)^[i] (p, u)).2).modelCountOn
      (Finset.range p.1) := by
  induction i generalizing u with
  | zero => exact hpos
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (modelCountOn_pos_preimageStepWith_canonical p u hpos)

/-- Final verification step of prefix self-reduction: check whether the candidate bitstring `st.2`
satisfies the formula `st.1.2`, returning `some st.2` if so and `none` otherwise. -/
def finishPreimageSearch (st : PreimageSearchState) : Option (List Bool) :=
  if st.1.2.eval (fun v => st.2.getD v false) then some st.2 else none

/-- Run `G.numVars` steps of prefix self-reduction with counter `count` and verify the resulting
candidate bitstring. -/
def findPreimageWith (k : ℕ) (count : ℕ × CNF ℕ → ℕ) (G : LocalMap) (target : List Bool) :
    Option (List Bool) :=
  finishPreimageSearch
    ((preimageStepWith count)^[G.numVars] (toDeclaredCNF k (G, target), []))

private theorem eval_toDeclaredCNF_getD (k : ℕ) (q : LocalMap × List Bool) (u : List Bool) :
    (toDeclaredCNF k q).2.eval (fun v => u.getD v false) =
      (q.1.Valid k && decide (q.1.evalBits u = q.2)) :=
  eval_toDeclaredCNF k q (fun v => u.getD v false)

/-- Canonical mathematical preimage finder for a `k`-local map `G` and target `target` via prefix
self-reduction. -/
def findPreimage (k : ℕ) (G : LocalMap) (target : List Bool) : Option (List Bool) :=
  findPreimageWith k canonicalDeclaredCount G target

private theorem findPreimageWith_eq_findPreimage {k : ℕ} {count : ℕ × CNF ℕ → ℕ}
    (hcount : ∀ p : ℕ × CNF ℕ, validDeclaredInput (max 1 k) p.1 p.2 = true →
      count p = canonicalDeclaredCount p)
    (G : LocalMap) (target : List Bool) :
    findPreimageWith k count G target = G.findPreimage k target := by
  simp only [findPreimage, findPreimageWith]
  congr 1
  exact iterate_preimageStepWith_congr hcount
    (validDeclaredInput_toDeclaredCNF (le_max_right 1 k) (G, target)) G.numVars [] (by simp)

/-- **Soundness of `findPreimage`:** Whenever `G.findPreimage k target = some x`, `G` is `k`-valid,
`x` has length `G.numVars`, and `G.evalBits x = target`. -/
theorem findPreimage_eq_some {k : ℕ} {G : LocalMap} {target x : List Bool}
    (h : G.findPreimage k target = some x) :
    G.Valid k = true ∧ x.length = G.numVars ∧ G.evalBits x = target := by
  simp only [findPreimage, findPreimageWith, finishPreimageSearch,
    iterate_preimageStepWith_fst, eval_toDeclaredCNF_getD] at h
  split_ifs at h with hcond
  · simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    refine ⟨hcond.1, ?_, hcond.2⟩
    simp [length_snd_iterate_preimageStepWith]

/-- **Completeness of `findPreimage`:** For any valid `k`-local map `G` and target `target` with
`0 < G.preimageCount target`, `G.findPreimage k target` returns `some x` for an `n`-bit preimage
`x` of `target`. -/
theorem findPreimage_isSome_of_preimageCount_pos {k : ℕ} {G : LocalMap} (hG : G.Valid k = true)
    {target : List Bool} (hpos : 0 < G.preimageCount target) :
    (G.findPreimage k target).isSome = true := by
  let p := toDeclaredCNF k (G, target)
  let u := ((preimageStepWith canonicalDeclaredCount)^[G.numVars] (p, [])).2
  have hu_len : u.length = G.numVars := by
    simp [u]
  have h0 : 0 < (p.2 ++ prefixUnits []).modelCountOn (Finset.range p.1) := by
    simp only [p, prefixUnits_nil, List.append_nil, modelCountOn_toDeclaredCNF, hG, ↓reduceIte]
    exact hpos
  have hfinal := modelCountOn_pos_iterate_preimageStepWith_canonical p G.numVars [] h0
  rw [CNF.modelCountOn, Finset.card_pos, Finset.filter_nonempty_iff] at hfinal
  obtain ⟨σ, -, hσ⟩ := hfinal
  simp only [CNF.eval_append, Bool.and_eq_true, eval_prefixUnits] at hσ
  have heval_p : p.2.eval (fun v => u.getD v false) = true := by
    rw [eval_toDeclaredCNF_getD, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hG, ?_⟩
    have hσ1 : G.eval (fun v => if h : v ∈ Finset.range p.1 then σ ⟨v, h⟩ else false) = target := by
      have h1 := hσ.1
      rwa [eval_toDeclaredCNF, hG, Bool.true_and, decide_eq_true_eq] at h1
    rw [LocalMap.evalBits, ← hσ1]
    refine G.eval_congr hG fun v hv => ?_
    exact (hσ.2 v (hu_len.symm ▸ hv)).symm
  simp only [findPreimage, findPreimageWith, finishPreimageSearch,
    iterate_preimageStepWith_fst]
  change (if p.2.eval (fun v => u.getD v false) then some u else none).isSome = true
  simp only [heval_p, ↓reduceIte, Option.isSome_some]

/-- For a valid `k`-local map `G`, `G.findPreimage k target` returns `some x` if and only if
`0 < G.preimageCount target`. -/
theorem findPreimage_isSome_iff {k : ℕ} {G : LocalMap} (hG : G.Valid k = true)
    (target : List Bool) :
    (G.findPreimage k target).isSome = true ↔ 0 < G.preimageCount target := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨_, hxlen, hxeval⟩ := findPreimage_eq_some hx
    exact (G.preimageCount_pos_iff hG target).mpr ⟨x, hxlen, hxeval⟩
  · exact findPreimage_isSome_of_preimageCount_pos hG

/-- For a valid `k`-local map `G`, `G.findPreimage k target` returns `none` if and only if
`G.preimageCount target = 0`. -/
theorem findPreimage_eq_none_iff {k : ℕ} {G : LocalMap} (hG : G.Valid k = true)
    (target : List Bool) :
    G.findPreimage k target = none ↔ G.preimageCount target = 0 := by
  rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, ← Bool.not_eq_true,
    findPreimage_isSome_iff hG, Nat.pos_iff_ne_zero, not_not]

section SelfReductionPolyTime

open ComputableInPolyTime

private theorem computableInPolyTime_prefixUnits :
    ComputableInPolyTime prefixUnits encBits encCNF := by
  have hrange : ComputableInPolyTime (fun u : List Bool => List.range u.length)
      encBits (encList encUnary) :=
    range.comp length_bits
  have hj : ComputableInPolyTime (fun p : List Bool × ℕ => p.2)
      (encPair encBits encUnary) encNat :=
    unary_to_binary.comp (snd encBits encUnary)
  have hbit : ComputableInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 false)
      (encPair encBits encUnary) encBool :=
    bitsGetD false
  have hcl : ComputableInPolyTime
      (fun p : List Bool × ℕ => [(p.2, p.1.getD p.2 false)])
      (encPair encBits encUnary) (encList (encPair encNat encBool)) :=
    cons' (hj.prod hbit) (const [])
  exact mapWithInput hrange hcl

private theorem computableInPolyTime_makePreimageQuery :
    ComputableInPolyTime makePreimageQuery encPreimageSearchState (encPair encUnary encCNF) := by
  have hst1 := fst (encPair encUnary encCNF) encBits
  have hst2 := snd (encPair encUnary encCNF) encBits
  have hu0 : ComputableInPolyTime
      (fun st : PreimageSearchState => st.2 ++ [false]) encPreimageSearchState encBits :=
    bitsAppend hst2 (const [false])
  have hunits : ComputableInPolyTime
      (fun st : PreimageSearchState => prefixUnits (st.2 ++ [false]))
      encPreimageSearchState encCNF :=
    computableInPolyTime_prefixUnits.comp hu0
  have hphi : ComputableInPolyTime
      (fun st : PreimageSearchState => st.1.2 ++ prefixUnits (st.2 ++ [false]))
      encPreimageSearchState encCNF :=
    listAppend' ((snd encUnary encCNF).comp hst1) hunits
  exact ((fst encUnary encCNF).comp hst1).prod hphi

private theorem computableInPolyTime_finishPreimageSearch :
    ComputableInPolyTime finishPreimageSearch encPreimageSearchState (encOption encBits) := by
  have hget : ComputableInPolyTime
      (fun p : (PreimageSearchState × Clause ℕ) × Literal ℕ =>
        (p.1.1.2.getD p.2.1 false) == p.2.2)
      (encPair (encPair encPreimageSearchState (encList (encPair encNat encBool)))
        (encPair encNat encBool))
      encBool := by
    have hu : ComputableInPolyTime
        (fun p : (PreimageSearchState × Clause ℕ) × Literal ℕ => p.1.1.2)
        (encPair (encPair encPreimageSearchState (encList (encPair encNat encBool)))
          (encPair encNat encBool))
        encBits :=
      (snd (encPair encUnary encCNF) encBits).comp ((fst _ _).comp (fst _ _))
    have hv : ComputableInPolyTime
        (fun p : (PreimageSearchState × Clause ℕ) × Literal ℕ => p.2.1)
        (encPair (encPair encPreimageSearchState (encList (encPair encNat encBool)))
          (encPair encNat encBool))
        encNat :=
      (fst encNat encBool).comp (snd _ _)
    have hpol : ComputableInPolyTime
        (fun p : (PreimageSearchState × Clause ℕ) × Literal ℕ => p.2.2)
        (encPair (encPair encPreimageSearchState (encList (encPair encNat encBool)))
          (encPair encNat encBool))
        encBool :=
      (snd encNat encBool).comp (snd _ _)
    exact beq (listGetD_binary false hu hv) hpol
  have hcl : ComputableInPolyTime
      (fun p : PreimageSearchState × Clause ℕ =>
        p.2.any fun l => (p.1.2.getD l.1 false) == l.2)
      (encPair encPreimageSearchState (encList (encPair encNat encBool))) encBool :=
    anyWithInput (snd _ _) hget
  have hphi : ComputableInPolyTime
      (fun st : PreimageSearchState => st.1.2) encPreimageSearchState encCNF :=
    (snd encUnary encCNF).comp (fst _ _)
  have heval : ComputableInPolyTime
      (fun st : PreimageSearchState =>
        st.1.2.all fun cl => cl.any fun l => (st.2.getD l.1 false) == l.2)
      encPreimageSearchState encBool :=
    allWithInput hphi hcl
  exact heval.ite ((optionSome encBits).comp (snd _ _)) (const none)

end SelfReductionPolyTime

end LocalMap

namespace CountingNativeEndpoint

open SubexponentialSAT ComputableInPolyTime LocalMap

private theorem numVars_le_length_encLocalMapQuery (q : LocalMap × List Bool) :
    q.1.numVars ≤ (encLocalMapQuery q).length := by
  simp only [encLocalMapQuery, encLocalMap, LocalMap.numVars, length_encPair, encUnary_apply,
    List.length_replicate]
  omega

/-- **Declared-form local map preimage finder (Corollary C.2):** For every fixed locality bound
`k`, `LocalMap.findPreimage k` is computed on native multi-tape Turing machines in time
$2^{O_k(\mathrm{interpolationScale}(n))} \cdot \mathrm{poly}(L)$ and polynomial space
$\mathrm{poly}(L)$. -/
public theorem exists_localMapPreimageFinder_declared (k : ℕ) :
    ∃ (T S : LocalMap × List Bool → ℕ) (A c e a b : ℕ),
      ComputableInO (fun q : LocalMap × List Bool => q.1.findPreimage k q.2)
        encLocalMapQuery (encOption encBits) T S ∧
      (∀ q : LocalMap × List Bool,
        (T q : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) *
          (((encLocalMapQuery q).length : ℝ) + 1) ^ e) + c) ∧
      (∀ q : LocalMap × List Bool, S q ≤ a * ((encLocalMapQuery q).length + 1) ^ b) := by
  obtain ⟨count, T₀, S₀, A, c, e, a, b, hcount, hspec, hT₀, hS₀⟩ :=
    exists_declaredCounter (max 1 k)
  have hcount_valid : ∀ p : ℕ × CNF ℕ, validDeclaredInput (max 1 k) p.1 p.2 = true →
      count p = canonicalDeclaredCount p := by
    intro p hp
    simp [hspec p, hp, canonicalDeclaredCount]
  -- Step 1: n(q) = q.1.numVars in binary
  have hn_polytime : ComputableInPolyTime (fun q : LocalMap × List Bool => q.1.numVars)
      encLocalMapQuery encNat :=
    unary_to_binary.comp ((fst encUnary (encList encLocalOutput)).comp (fst encLocalMap encBits))
  obtain ⟨dn, _, hdn⟩ := hn_polytime.exists_degree
  have hn : ComputableInO (fun q : LocalMap × List Bool => q.1.numVars)
      encLocalMapQuery encNat
      (fun q => ((encLocalMapQuery q).length + 1) ^ dn)
      (fun q => ((encLocalMapQuery q).length + 1) ^ dn) :=
    hdn.inO
  -- Step 2: init(q) = (toDeclaredCNF k q, [])
  have hinit_polytime : ComputableInPolyTime
      (fun q : LocalMap × List Bool => (toDeclaredCNF k q, ([] : List Bool)))
      encLocalMapQuery encPreimageSearchState :=
    (computableInPolyTime_toDeclaredCNF k).prod (const [])
  obtain ⟨di, _, hdi⟩ := hinit_polytime.exists_degree
  have hinit : ComputableInO
      (fun q : LocalMap × List Bool => (toDeclaredCNF k q, ([] : List Bool)))
      encLocalMapQuery encPreimageSearchState
      (fun q => ((encLocalMapQuery q).length + 1) ^ di)
      (fun q => ((encLocalMapQuery q).length + 1) ^ di) :=
    hdi.inO
  -- Step 3: step = preimageStepWith count
  obtain ⟨d_mk, _, hd_mk⟩ := computableInPolyTime_makePreimageQuery.exists_degree
  obtain ⟨p_mk, q_mk, hp_mk⟩ := computableInPolyTime_makePreimageQuery.polyBounded_length.exists_le
  have hnext : ComputableInO (fun st : PreimageSearchState => count (makePreimageQuery st) == 0)
      encPreimageSearchState encBool
      (fun st => ((encPreimageSearchState st).length + 1) ^ d_mk + T₀ (makePreimageQuery st))
      (fun st => ((encPreimageSearchState st).length + 1) ^ d_mk + S₀ (makePreimageQuery st)) :=
    (ComputableInO.natIsZero.comp_linear hcount).comp hd_mk.inO
  have hstep : ComputableInO (preimageStepWith count)
      encPreimageSearchState encPreimageSearchState
      (fun st => (encPreimageSearchState st).length +
        (((encPreimageSearchState st).length + 1) ^ d_mk + T₀ (makePreimageQuery st)))
      (fun st => (encPreimageSearchState st).length +
        (((encPreimageSearchState st).length + 1) ^ d_mk + S₀ (makePreimageQuery st))) :=
    (ComputableInO.of_eq (encIn := encPreimageSearchState) (encMid := encPreimageSearchState)
      fun _ => rfl).append hnext fun st => by
        simp [preimageStepWith, encPreimageSearchState, encPair_apply, encBits_apply,
          encBool_apply, List.append_assoc]
  -- Step 4: Trajectory bounds B, M, R, Q
  let B (q : LocalMap × List Bool) : ℕ :=
    2 * (encPair encUnary encCNF (toDeclaredCNF k q)).length + 1 + q.1.numVars
  have hstate : ∀ (q : LocalMap × List Bool) (i : ℕ), i ≤ q.1.numVars →
      (encPreimageSearchState
        ((preimageStepWith count)^[i] (toDeclaredCNF k q, []))).length ≤ B q := by
    intro q i hi
    simp only [encPreimageSearchState, length_encPair, iterate_preimageStepWith_fst,
      encBits_apply, length_snd_iterate_preimageStepWith, List.length_nil, Nat.zero_add, B]
    omega
  let M (q : LocalMap × List Bool) : ℕ := p_mk * (B q + 1) ^ q_mk
  have hM_le : ∀ (q : LocalMap × List Bool) (i : ℕ), i ≤ q.1.numVars →
      (encPair encUnary encCNF
        (makePreimageQuery ((preimageStepWith count)^[i] (toDeclaredCNF k q, [])))).length ≤
        M q := by
    intro q i hi
    let st := (preimageStepWith count)^[i] (toDeclaredCNF k q, [])
    exact (hp_mk st).trans
      (Nat.mul_le_mul_left p_mk (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate q i hi) 1) q_mk))
  let N_exp (q : LocalMap × List Bool) : ℕ :=
    ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars)⌉₊
  let R (q : LocalMap × List Bool) : ℕ :=
    B q + ((B q + 1) ^ d_mk + (c * N_exp q * (M q + 1) ^ e + c))
  let Q (q : LocalMap × List Bool) : ℕ :=
    B q + ((B q + 1) ^ d_mk + a * (M q + 1) ^ b)
  have hround : ∀ (q : LocalMap × List Bool) (i : ℕ), i ≤ q.1.numVars →
      (let st := (preimageStepWith count)^[i] (toDeclaredCNF k q, [])
       (encPreimageSearchState st).length +
        (((encPreimageSearchState st).length + 1) ^ d_mk + T₀ (makePreimageQuery st))) ≤
        R q := by
    intro q i hi
    dsimp only [R]
    have hst_len := hstate q i hi
    have hmk_len := hM_le q i hi
    have hmk_fst :
        (makePreimageQuery ((preimageStepWith count)^[i] (toDeclaredCNF k q, []))).1 =
          q.1.numVars := by
      simp [makePreimageQuery, iterate_preimageStepWith_fst]
    have hT_mk :
        T₀ (makePreimageQuery ((preimageStepWith count)^[i] (toDeclaredCNF k q, []))) ≤
          c * N_exp q * (M q + 1) ^ e + c := by
      have h := hT₀ (makePreimageQuery ((preimageStepWith count)^[i] (toDeclaredCNF k q, [])))
      rw [hmk_fst] at h
      have hXN : (2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) ≤ N_exp q :=
        Nat.le_ceil _
      have hpow :
          (((encPair encUnary encCNF
            (makePreimageQuery ((preimageStepWith count)^[i] (toDeclaredCNF k q, [])))).length : ℝ)
              + 1) ^ e ≤ ((M q : ℝ) + 1) ^ e := by
        exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hmk_len 1) e
      have h1 := mul_le_mul hXN hpow (by positivity) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c)
      have h3 : (c : ℝ) * ((N_exp q : ℝ) * ((M q : ℝ) + 1) ^ e) =
          ((c * N_exp q * (M q + 1) ^ e : ℕ) : ℝ) := by push_cast; ring
      have : (T₀ (makePreimageQuery ((preimageStepWith count)^[i] (toDeclaredCNF k q, []))) : ℝ) ≤
          ((c * N_exp q * (M q + 1) ^ e + c : ℕ) : ℝ) := by
        push_cast at h3 ⊢
        linarith
      exact_mod_cast this
    have hpow_dmk :
        ((encPreimageSearchState
          ((preimageStepWith count)^[i] (toDeclaredCNF k q, []))).length + 1) ^ d_mk ≤
          (B q + 1) ^ d_mk :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hst_len 1) d_mk
    omega
  have hspace : ∀ (q : LocalMap × List Bool) (i : ℕ), i ≤ q.1.numVars →
      (let st := (preimageStepWith count)^[i] (toDeclaredCNF k q, [])
       (encPreimageSearchState st).length +
        (((encPreimageSearchState st).length + 1) ^ d_mk + S₀ (makePreimageQuery st))) ≤
        Q q := by
    intro q i hi
    dsimp only [Q]
    have hst_len := hstate q i hi
    have hmk_len := hM_le q i hi
    have hS_mk :
        S₀ (makePreimageQuery ((preimageStepWith count)^[i] (toDeclaredCNF k q, []))) ≤
          a * (M q + 1) ^ b :=
      (hS₀ (makePreimageQuery ((preimageStepWith count)^[i] (toDeclaredCNF k q, [])))).trans
        (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hmk_len 1) b))
    have hpow_dmk :
        ((encPreimageSearchState
          ((preimageStepWith count)^[i] (toDeclaredCNF k q, []))).length + 1) ^ d_mk ≤
          (B q + 1) ^ d_mk :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hst_len 1) d_mk
    omega
  have hiter := ComputableInO.iterate hn hinit hstep hround hspace hstate
  -- Step 5: Post-compose with finishPreimageSearch
  obtain ⟨df, _, hdf⟩ := computableInPolyTime_finishPreimageSearch.exists_degree
  have hfin : ComputableInO finishPreimageSearch encPreimageSearchState (encOption encBits)
      (fun st => ((encPreimageSearchState st).length + 1) ^ df)
      (fun st => ((encPreimageSearchState st).length + 1) ^ df) :=
    hdf.inO
  have hcomp : ComputableInO (fun q : LocalMap × List Bool => q.1.findPreimage k q.2)
      encLocalMapQuery (encOption encBits) _ _ :=
    (hfin.comp hiter).of_enc_eq fun q => by
      change encOption encBits (q.1.findPreimage k q.2) =
        encOption encBits (findPreimageWith k count q.1 q.2)
      rw [LocalMap.findPreimageWith_eq_findPreimage hcount_valid q.1 q.2]
  -- Step 6: Polynomial bounds via PolyBounded
  let size (q : LocalMap × List Bool) : ℕ := (encLocalMapQuery q).length
  have hn_poly : PolyBounded size (fun q => q.1.numVars) :=
    PolyBounded.self.mono numVars_le_length_encLocalMapQuery
  have hB_poly : PolyBounded size B :=
    (((PolyBounded.const 2).mul
      (computableInPolyTime_toDeclaredCNF k).polyBounded_length).add (.const 1)).add hn_poly
  have hM_poly : PolyBounded size M :=
    (PolyBounded.const p_mk).mul ((hB_poly.add (.const 1)).pow q_mk)
  have hQ_poly : PolyBounded size Q :=
    hB_poly.add (((hB_poly.add (.const 1)).pow d_mk).add
      ((PolyBounded.const a).mul ((hM_poly.add (.const 1)).pow b)))
  have hencNat_n_le (q : LocalMap × List Bool) :
      (encNat q.1.numVars).length ≤ size q := by
    have h1 : (encNat q.1.numVars).length ≤ q.1.numVars := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_self q.1.numVars
    exact h1.trans (numVars_le_length_encLocalMapQuery q)
  have hencNat_poly : PolyBounded size (fun q => (encNat q.1.numVars).length) :=
    PolyBounded.self.mono hencNat_n_le
  let R_poly (q : LocalMap × List Bool) : ℕ :=
    B q + (B q + 1) ^ d_mk + c * (M q + 1) ^ e + c
  have hR_poly : PolyBounded size R_poly :=
    ((hB_poly.add ((hB_poly.add (.const 1)).pow d_mk)).add
      ((PolyBounded.const c).mul ((hM_poly.add (.const 1)).pow e))).add (.const c)
  let T_poly (q : LocalMap × List Bool) : ℕ :=
    (size q + 1) ^ dn + (size q + 1) ^ di +
      (q.1.numVars + 1) * (R_poly q + B q + ((encNat q.1.numVars).length + 1) ^ 2) +
      (B q + 1) ^ df
  have hT_poly : PolyBounded size T_poly :=
    ((((PolyBounded.self.add (.const 1)).pow dn).add
      ((PolyBounded.self.add (.const 1)).pow di)).add
      ((hn_poly.add (.const 1)).mul
        ((hR_poly.add hB_poly).add ((hencNat_poly.add (.const 1)).pow 2)))).add
      ((hB_poly.add (.const 1)).pow df)
  let S_poly (q : LocalMap × List Bool) : ℕ :=
    (size q + 1) ^ dn + (size q + 1) ^ di + Q q + B q +
      (encNat q.1.numVars).length + (B q + 1) ^ df
  have hS_poly : PolyBounded size S_poly :=
    ((((((PolyBounded.self.add (.const 1)).pow dn).add
      ((PolyBounded.self.add (.const 1)).pow di)).add hQ_poly).add hB_poly).add
      hencNat_poly).add ((hB_poly.add (.const 1)).pow df)
  obtain ⟨C_T, d_T, hCT⟩ := hT_poly.exists_le
  obtain ⟨C_S, d_S, hCS⟩ := hS_poly.exists_le
  refine ⟨_, _, A, 2 * C_T + 1, d_T, C_S, d_S, hcomp, fun q => ?_, fun q => ?_⟩
  · have hN1 : 1 ≤ N_exp q :=
      Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hR_le : R q ≤ N_exp q * R_poly q := by
      dsimp only [R, R_poly]
      have h1 : B q + (B q + 1) ^ d_mk + c ≤
          N_exp q * (B q + (B q + 1) ^ d_mk + c) :=
        Nat.le_mul_of_pos_left _ hN1
      have h2 : c * N_exp q * (M q + 1) ^ e = N_exp q * (c * (M q + 1) ^ e) := by ring
      nlinarith
    have hfin_le :
        ((encPreimageSearchState
          ((preimageStepWith count)^[q.1.numVars] (toDeclaredCNF k q, []))).length + 1) ^ df ≤
        (B q + 1) ^ df :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (hstate q q.1.numVars le_rfl) 1) df
    have hT_le_N :
        ((size q + 1) ^ dn + (size q + 1) ^ di +
          (q.1.numVars + 1) * (R q + B q + ((encNat q.1.numVars).length + 1) ^ 2)) +
          ((encPreimageSearchState
            ((preimageStepWith count)^[q.1.numVars] (toDeclaredCNF k q, []))).length + 1) ^ df ≤
        N_exp q * T_poly q := by
      have hstep_le : R q + B q + ((encNat q.1.numVars).length + 1) ^ 2 ≤
          N_exp q * (R_poly q + B q + ((encNat q.1.numVars).length + 1) ^ 2) := by
        have := Nat.le_mul_of_pos_left (B q + ((encNat q.1.numVars).length + 1) ^ 2) hN1
        nlinarith
      have hmul_step := Nat.mul_le_mul_left (q.1.numVars + 1) hstep_le
      have hrest := Nat.le_mul_of_pos_left
        ((size q + 1) ^ dn + (size q + 1) ^ di + (B q + 1) ^ df) hN1
      dsimp only [T_poly]
      nlinarith
    have hT_le_poly : N_exp q * T_poly q ≤ N_exp q * (C_T * (size q + 1) ^ d_T) :=
      Nat.mul_le_mul_left _ (hCT q)
    have hscale : (0 : ℝ) ≤ (A : ℝ) * interpolationScale q.1.numVars :=
      mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg _)
    have hX1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) :=
      Real.one_le_rpow (by norm_num) hscale
    have hNX : (N_exp q : ℝ) ≤ 2 * (2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) := by
      have hlt : (N_exp q : ℝ) < (2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      linarith
    have htotal :
        ((((size q + 1) ^ dn + (size q + 1) ^ di +
          (q.1.numVars + 1) * (R q + B q + ((encNat q.1.numVars).length + 1) ^ 2)) +
          ((encPreimageSearchState
            ((preimageStepWith count)^[q.1.numVars] (toDeclaredCNF k q, []))).length + 1) ^ df :
          ℕ) : ℝ) ≤
        (N_exp q : ℝ) * (C_T * ((size q : ℝ) + 1) ^ d_T) := by
      exact_mod_cast hT_le_N.trans hT_le_poly
    have h2 : (N_exp q : ℝ) * (C_T * ((size q : ℝ) + 1) ^ d_T) ≤
        ((2 * C_T + 1 : ℕ) : ℝ) *
          ((2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) * ((size q : ℝ) + 1) ^ d_T) := by
      have hmul1 := mul_le_mul_of_nonneg_right hNX
        (by positivity : (0 : ℝ) ≤ C_T * ((size q : ℝ) + 1) ^ d_T)
      have hZ0 : (0 : ℝ) ≤
          (2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) * ((size q : ℝ) + 1) ^ d_T := by
        positivity
      have hring : ((2 * C_T + 1 : ℕ) : ℝ) *
          ((2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) * ((size q : ℝ) + 1) ^ d_T) =
          2 * (2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) *
            (C_T * ((size q : ℝ) + 1) ^ d_T) +
          (2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars) * ((size q : ℝ) + 1) ^ d_T := by
        push_cast; ring
      linarith
    have hc_nonneg : (0 : ℝ) ≤ ((2 * C_T + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    dsimp only [size] at htotal h2 ⊢
    push_cast at htotal h2 hc_nonneg ⊢
    linarith
  · have hfin_le :
        ((encPreimageSearchState
          ((preimageStepWith count)^[q.1.numVars] (toDeclaredCNF k q, []))).length + 1) ^ df ≤
        (B q + 1) ^ df :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (hstate q q.1.numVars le_rfl) 1) df
    exact (Nat.add_le_add_left hfin_le _).trans (hCS q)

/-- **Subexponential local map preimage finding (Corollary C.2):** For every fixed locality bound
`k`, one native machine computes `G.findPreimage k target` (returning `some x` with `x.length =
G.numVars` and `G.evalBits x = target` whenever `G` is `k`-valid and a preimage exists, and `none`
otherwise) within time `⌈2 ^ (A * interpolationScale G.numVars)⌉₊ * (L + 1) ^ e` and space
`(L + 1) ^ b`. -/
public theorem exists_localMapPreimageFinder (k : ℕ) :
    ∃ (find : LocalMap × List Bool → Option (List Bool)) (A e b : ℕ),
      (∀ q : LocalMap × List Bool, find q = q.1.findPreimage k q.2) ∧
      (∀ (q : LocalMap × List Bool) (x : List Bool),
        find q = some x →
          q.1.Valid k = true ∧ x.length = q.1.numVars ∧ q.1.evalBits x = q.2) ∧
      (∀ q : LocalMap × List Bool, q.1.Valid k = true →
        ((find q).isSome = true ↔ 0 < q.1.preimageCount q.2)) ∧
      ComputableInO find encLocalMapQuery (encOption encBits)
        (fun q => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale q.1.numVars)⌉₊ *
          ((encLocalMapQuery q).length + 1) ^ e)
        (fun q => ((encLocalMapQuery q).length + 1) ^ b) := by
  obtain ⟨T, S, A, c, e, a, b, hfind, hT, hS⟩ := exists_localMapPreimageFinder_declared k
  exact ⟨fun q => q.1.findPreimage k q.2, A, e, b,
    fun _ => rfl,
    fun _ _ hx => LocalMap.findPreimage_eq_some hx,
    fun q hG => LocalMap.findPreimage_isSome_iff hG q.2,
    computableInO_of_declared_localMap_bounds hfind hT hS⟩

end CountingNativeEndpoint

end Cslib.Complexity
