/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (the `Primcodable` coding of Mathlib's `L.BoundedFormula` is a named
-- definition with a scoped instance, so that it cannot clash with a future Mathlib instance)

public import CslibFrontier.Logics.FirstOrder.QuantifierRank
public import CslibFrontier.Logics.FirstOrder.Raw.Levels
public import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Fintype.Card

/-!
# Raw codes of Mathlib's bounded formulas

For a relational language `L` with an `Encodable` set of relation symbols, this module translates
Mathlib's `L.BoundedFormula α n` into the raw syntax `Cslib.Logic.FO.RawFormula` and back, and
uses the translation to make bounded formulas `Primcodable`.

`FirstOrder.Language.BoundedFormula.toRaw` renames variables by parity: the bound variable `&i` is
the raw variable `2 * i`, a free variable `a` is `2 * encode a + 1`, the `all` at depth `k` binds
`2 * k`, and a relation symbol `R : L.Relations l` is the number `encode ⟨l, R⟩`. Its image at
depth `n` is the set of raw formulas that are level-named in the sense of
`Cslib.Logic.FO.RawFormula.WellScoped`, with free names in the range of `encode` and symbol codes of
the right arity (`FirstOrder.Language.BoundedFormula.isSome_fromRaw`). The structural partial
inverse `FirstOrder.Language.BoundedFormula.fromRaw` is computable, so no choice is involved.

`FirstOrder.Language.BoundedFormula.primcodableRaw` codes `φ` by the code of `toRaw φ`; it needs
`[L.IsRelational]`, `[Encodable (Σ l, L.Relations l)]` and `[Finite (Σ l, L.Relations l)]`, the last
so that the set of symbol codes of a given arity is primitive recursive. It is a definition, not a
global instance: Mathlib has no `Primcodable` instance for bounded formulas, and if it gains one
(`Mathlib/ModelTheory/Encoding.lean` lists one as a TODO), a global instance here would form a
diamond. Clients write `open scoped FirstOrder.Language.BoundedFormula.RawCoding` to use it as an
instance. Up to primitive recursive equivalence the coding does not depend on the encoding of the
symbols: `id` is primitive recursive between the codings induced by two `Encodable` instances
(`FirstOrder.Language.BoundedFormula.primrec_id_primcodableRaw`).

The semantics agree: `toRaw φ` holds under a raw interpretation compatible with a structure, and an
assignment that sends `2 * i` and `2 * encode a + 1` to the values of `&i` and `a`, iff `φ` holds
(`FirstOrder.Language.BoundedFormula.realize_toRaw`). In particular a sentence is finitely
satisfiable, or finitely valid, iff its raw code is
(`FirstOrder.Language.Sentence.finSat_iff_toRaw`,
`FirstOrder.Language.Sentence.finValid_iff_toRaw`).
Trakhtenbrot's theorem for `L.Sentence` is derived from these in
`CslibFrontier/Logics/FirstOrder/Trakhtenbrot/Sentence.lean`.

## Main definitions

* `FirstOrder.Language.BoundedFormula.rawVar`, `FirstOrder.Language.BoundedFormula.varOfRaw`: raw
  names of variables.
* `FirstOrder.Language.BoundedFormula.toRaw`, `FirstOrder.Language.BoundedFormula.fromRaw`: the
  translation and its structural partial inverse.
* `FirstOrder.Language.BoundedFormula.primcodableRaw`: the `Primcodable` coding of bounded formulas,
  a scoped instance in `FirstOrder.Language.BoundedFormula.RawCoding`.
* `FirstOrder.Language.Sentence.FinSat`, `FirstOrder.Language.Sentence.FinValid`: truth in some or
  every finite nonempty structure.

## Main results

* `FirstOrder.Language.BoundedFormula.fromRaw_toRaw`,
  `FirstOrder.Language.BoundedFormula.toRaw_of_fromRaw`,
  `FirstOrder.Language.BoundedFormula.isSome_fromRaw`: `fromRaw` inverts `toRaw` on its image.
* `FirstOrder.Language.BoundedFormula.primrec_iff_primrec_toRaw`,
  `FirstOrder.Language.BoundedFormula.primrec_toRaw`,
  `FirstOrder.Language.BoundedFormula.primrec_fromRaw`: primitive recursiveness at the coding.
* `FirstOrder.Language.BoundedFormula.primrec_imp`,
  `FirstOrder.Language.BoundedFormula.primrec_all`,
  `FirstOrder.Language.BoundedFormula.primrec_not`, `FirstOrder.Language.BoundedFormula.primrec_ex`,
  `FirstOrder.Language.BoundedFormula.primrec_rel`,
  `FirstOrder.Language.BoundedFormula.primrec_equal`,
  `FirstOrder.Language.BoundedFormula.primrec_quantifierRank`: the constructors and quantifier rank
  are primitive recursive.
* `FirstOrder.Language.BoundedFormula.quantifierDepth_toRaw`: the quantifier depth of `toRaw φ` is
  the quantifier rank of `φ`.
* `FirstOrder.Language.BoundedFormula.primrec_id_primcodableRaw`: the coding does not depend on the
  choice of symbol encoding, up to primitive recursive equivalence.
* `FirstOrder.Language.BoundedFormula.realize_toRaw`: the translation preserves meaning.
* `FirstOrder.Language.Sentence.exists_structure_realize_iff_toRaw`,
  `FirstOrder.Language.Sentence.finSat_iff_toRaw`,
  `FirstOrder.Language.Sentence.finValid_iff_toRaw`: satisfaction on a given nonempty carrier,
  finite satisfiability and finite validity transfer.
-/

public section

namespace FirstOrder.Language

open Encodable Cslib.Logic.FO

variable {L : Language} {α : Type*} {n : ℕ}

namespace BoundedFormula

/-! ### Raw names of variables -/

section Vars

variable [Encodable α]

/-- The raw name of a variable: the bound variable `i` is `2 * i`, the free variable `a` is
`2 * encode a + 1`. -/
@[expose]
def rawVar : α ⊕ Fin n → ℕ
  | .inl a => 2 * encode a + 1
  | .inr i => 2 * i

/-- The variable with a given raw name at depth `n`, if any. -/
def varOfRaw (n y : ℕ) : Option (α ⊕ Fin n) :=
  if h : y % 2 = 0 ∧ y / 2 < n then some (.inr ⟨y / 2, h.2⟩)
  else if y % 2 = 1 then (decode₂ α (y / 2)).map .inl else none

@[simp]
theorem rawVar_inl (a : α) : rawVar (n := n) (.inl a) = 2 * encode a + 1 := rfl

@[simp]
theorem rawVar_inr (i : Fin n) : rawVar (α := α) (.inr i) = 2 * i := rfl

@[simp]
theorem varOfRaw_rawVar (v : α ⊕ Fin n) : varOfRaw n (rawVar v) = some v := by
  rcases v with a | i
  · have h1 : (2 * encode a + 1) % 2 = 1 := by omega
    have h2 : (2 * encode a + 1) / 2 = encode a := by omega
    simp [varOfRaw, h1, h2]
  · have h1 : 2 * (i : ℕ) % 2 = 0 := by omega
    have h2 : 2 * (i : ℕ) / 2 = i := by omega
    simp [varOfRaw, h1, h2]

theorem rawVar_of_varOfRaw {y : ℕ} {v : α ⊕ Fin n} (h : varOfRaw n y = some v) :
    rawVar v = y := by
  unfold varOfRaw at h
  split_ifs at h with h1 h2
  · cases h
    simp only [rawVar_inr]
    omega
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [rawVar_inl, decode₂_eq_some.1 ha]
    omega

theorem isSome_varOfRaw {y : ℕ} :
    (varOfRaw (α := α) n y).isSome ↔ RawFormula.NameOk (· ∈ Set.range (encode : α → ℕ)) n y := by
  unfold varOfRaw RawFormula.NameOk
  split_ifs with h1 h2
  · simp only [Option.isSome_some, true_iff]
    exact Or.inl h1
  · rw [Option.isSome_map, Option.isSome_iff_exists]
    simp only [decode₂_eq_some, Set.mem_range]
    constructor
    · rintro ⟨a, ha⟩
      exact Or.inr ⟨h2, a, ha⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · omega
      · exact h
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    omega

end Vars

/-! ### The translation -/

section Translation

variable [Encodable α]

section Terms

variable [L.IsRelational]

/-- The raw name of a term: terms of a relational language are variables. -/
@[expose]
def rawTerm : L.Term (α ⊕ Fin n) → ℕ
  | .var v => rawVar v
  | .func f _ => isEmptyElim f

@[simp]
theorem rawTerm_var (v : α ⊕ Fin n) : rawTerm (L := L) (.var v) = rawVar v := rfl

omit [Encodable α] in
private theorem term_eq_var (t : L.Term (α ⊕ Fin n)) : ∃ v, t = .var v := by
  rcases t with v | ⟨f, _⟩
  · exact ⟨v, rfl⟩
  · exact isEmptyElim f

end Terms

variable [Encodable (Σ l, L.Relations l)]

/-- The relation atom with raw symbol code `r` and raw argument names `ys` at depth `n`, if the code
names a relation symbol of arity `ys.length` and every name is a variable at depth `n`. -/
def relOfRaw (n r : ℕ) (ys : List ℕ) : Option (L.BoundedFormula α n) :=
  (decode₂ (Σ l, L.Relations l) r).bind fun R =>
    if h : ys.length = R.1 ∧ ∀ y ∈ ys, (varOfRaw (α := α) n y).isSome then
      some (rel R.2 fun i => .var ((varOfRaw n ys[i]).get
        (h.2 _ (List.getElem_mem (by rw [h.1]; exact i.isLt)))))
    else none

/-- The bounded formula at depth `n` with a given raw formula, if any: the structural partial
inverse of `toRaw`. -/
def fromRaw : (n : ℕ) → RawFormula → Option (L.BoundedFormula α n)
  | _, .falsum => some falsum
  | n, .equal x y => Option.map₂ (fun v w => equal (.var v) (.var w)) (varOfRaw n x) (varOfRaw n y)
  | n, .rel r ys => relOfRaw n r ys
  | n, .imp φ ψ => Option.map₂ imp (fromRaw n φ) (fromRaw n ψ)
  | n, .all x φ => if x = 2 * n then (fromRaw (n + 1) φ).map all else none

private theorem isSome_map₂ {β γ δ : Type*} {f : β → γ → δ} {a : Option β} {b : Option γ} :
    (Option.map₂ f a b).isSome ↔ a.isSome ∧ b.isSome := by
  cases a <;> cases b <;> simp

/-- `fromRaw n χ` is defined iff `χ` is level-named at depth `n`, with free names in the range of
`encode` and symbol codes naming relation symbols of the right arity. -/
theorem isSome_fromRaw : ∀ {n} {χ : RawFormula},
    (fromRaw (L := L) (α := α) n χ).isSome ↔
      RawFormula.WellScoped (· ∈ Set.range (encode : α → ℕ))
        (fun r k => ∃ R : Σ l, L.Relations l, encode R = r ∧ R.1 = k) n χ
  | _, .falsum => by simp [fromRaw, RawFormula.WellScoped]
  | n, .equal x y => by
    rw [fromRaw, isSome_map₂, isSome_varOfRaw, isSome_varOfRaw]
    rfl
  | n, .rel r ys => by
    rw [fromRaw, relOfRaw, RawFormula.WellScoped]
    simp only [← isSome_varOfRaw]
    cases hR : decode₂ (Σ l, L.Relations l) r with
    | none =>
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
      rintro ⟨R, rfl, -⟩
      simp at hR
    | some R =>
      have hr := decode₂_eq_some.1 hR
      rw [Option.bind_some]
      split_ifs with hc
      · simp only [Option.isSome_some, true_iff]
        exact ⟨⟨R, hr, hc.1.symm⟩, hc.2⟩
      · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
        rintro ⟨R', hR', hl⟩ hs
        obtain rfl := encode_injective (hR'.trans hr.symm)
        exact hc ⟨hl.symm, hs⟩
  | n, .imp χ₁ χ₂ => by
    rw [fromRaw, isSome_map₂, isSome_fromRaw, isSome_fromRaw]
    rfl
  | n, .all x χ => by
    rw [fromRaw, RawFormula.WellScoped]
    split_ifs with hx
    · rw [Option.isSome_map, isSome_fromRaw]
      simp [hx]
    · simp [hx]

variable [L.IsRelational]

/-- The raw formula of a bounded formula: the bound variable `&i` is named `2 * i`, a free variable
`a` is named `2 * encode a + 1`, the quantifier at depth `k` binds `2 * k`, and `R : L.Relations l`
is the symbol `encode ⟨l, R⟩`. -/
@[expose]
def toRaw : ∀ {n}, L.BoundedFormula α n → RawFormula
  | _, falsum => .falsum
  | _, equal t₁ t₂ => .equal (rawTerm t₁) (rawTerm t₂)
  | _, @rel _ _ _ l R ts =>
    .rel (encode (⟨l, R⟩ : Σ l, L.Relations l)) (List.ofFn fun i => rawTerm (ts i))
  | _, imp φ ψ => .imp (toRaw φ) (toRaw ψ)
  | n, all φ => .all (2 * n) (toRaw φ)

@[simp]
theorem toRaw_falsum : (falsum : L.BoundedFormula α n).toRaw = .falsum := rfl

@[simp]
theorem toRaw_bot : (⊥ : L.BoundedFormula α n).toRaw = .falsum := rfl

@[simp]
theorem toRaw_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂).toRaw = .equal (rawTerm t₁) (rawTerm t₂) := rfl

@[simp]
theorem toRaw_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts).toRaw =
      .rel (encode (⟨l, R⟩ : Σ l, L.Relations l)) (List.ofFn fun i => rawTerm (ts i)) :=
  rfl

@[simp]
theorem toRaw_imp (φ ψ : L.BoundedFormula α n) : (imp φ ψ).toRaw = .imp φ.toRaw ψ.toRaw := rfl

@[simp]
theorem toRaw_all (φ : L.BoundedFormula α (n + 1)) : (all φ).toRaw = .all (2 * n) φ.toRaw := rfl

@[simp]
theorem toRaw_not (φ : L.BoundedFormula α n) : φ.not.toRaw = RawFormula.neg φ.toRaw := rfl

@[simp]
theorem quantifierDepth_toRaw : ∀ {n} (φ : L.BoundedFormula α n),
    φ.toRaw.quantifierDepth = quantifierRank φ
  | _, falsum => quantifierRank_falsum.symm
  | _, equal _ _ => (quantifierRank_equal _ _).symm
  | _, rel _ _ => (quantifierRank_rel _ _).symm
  | _, imp φ ψ => by
    simp only [toRaw_imp, RawFormula.quantifierDepth_imp, quantifierRank_imp,
      quantifierDepth_toRaw φ, quantifierDepth_toRaw ψ]
  | _, all φ => by
    simp only [toRaw_all, RawFormula.quantifierDepth_all, quantifierRank_all,
      quantifierDepth_toRaw φ]

theorem fromRaw_toRaw : ∀ {n} (φ : L.BoundedFormula α n), fromRaw n φ.toRaw = some φ
  | _, falsum => rfl
  | n, equal t₁ t₂ => by
    obtain ⟨v, rfl⟩ := term_eq_var t₁
    obtain ⟨w, rfl⟩ := term_eq_var t₂
    simp [fromRaw]
  | n, @rel _ _ _ l R ts => by
    have hs : ∀ y ∈ List.ofFn (fun i => rawTerm (ts i)), (varOfRaw (α := α) n y).isSome := by
      intro y hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      obtain ⟨v, hv⟩ := term_eq_var (ts i)
      simp [hv]
    rw [toRaw_rel, fromRaw, relOfRaw, encodek₂, Option.bind_some,
      dite_eq_left ⟨List.length_ofFn, hs⟩]
    congr 2
    funext i
    obtain ⟨v, hv⟩ := term_eq_var (ts i)
    have key : ∀ (y : ℕ) (h : (varOfRaw (α := α) n y).isSome), y = rawVar v →
        Term.var (L := L) ((varOfRaw n y).get h) = ts i := by
      rintro y h rfl
      rw [hv, Option.get_of_eq_some h (varOfRaw_rawVar v)]
    exact key _ _ (by simp [hv])
  | _, imp φ ψ => by
    rw [toRaw_imp, fromRaw, fromRaw_toRaw φ, fromRaw_toRaw ψ]
    rfl
  | n, all φ => by
    rw [toRaw_all, fromRaw, ite_eq_left rfl, fromRaw_toRaw φ]
    rfl

theorem toRaw_of_fromRaw :
    ∀ {n} {χ : RawFormula} {φ : L.BoundedFormula α n}, fromRaw n χ = some φ → φ.toRaw = χ
  | _, .falsum, _, h => by
    cases h
    rfl
  | n, .equal x y, _, h => by
    rw [fromRaw, Option.map₂_eq_some_iff] at h
    obtain ⟨v, w, hv, hw, rfl⟩ := h
    simp [rawVar_of_varOfRaw hv, rawVar_of_varOfRaw hw]
  | n, .rel r ys, φ, h => by
    rw [fromRaw, relOfRaw, Option.bind_eq_some_iff] at h
    obtain ⟨R, hR, h⟩ := h
    split_ifs at h with hc
    cases h
    rw [toRaw_rel]
    congr 1
    · exact decode₂_eq_some.1 hR
    · refine List.ext_getElem (by simp [hc.1]) fun i h₁ h₂ => ?_
      simp only [List.getElem_ofFn, rawTerm_var]
      exact rawVar_of_varOfRaw (Option.some_get _).symm
  | n, .imp χ₁ χ₂, _, h => by
    rw [fromRaw, Option.map₂_eq_some_iff] at h
    obtain ⟨φ, ψ, hφ, hψ, rfl⟩ := h
    rw [toRaw_imp, toRaw_of_fromRaw hφ, toRaw_of_fromRaw hψ]
  | n, .all x χ, _, h => by
    rw [fromRaw] at h
    split_ifs at h with hx
    obtain ⟨φ, hφ, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [toRaw_all, toRaw_of_fromRaw hφ, hx]

/-- The `Encodable` structure coding a bounded formula by the code of its raw formula. -/
@[instance_reducible]
private def encodableRaw : Encodable (L.BoundedFormula α n) :=
  Encodable.ofLeftInjection toRaw (fromRaw n) fromRaw_toRaw

end Translation

/-! ### The `Primcodable` coding -/

section Coding

variable [Primcodable α] [Encodable (Σ l, L.Relations l)] [Finite (Σ l, L.Relations l)]
  [L.IsRelational]

omit [L.IsRelational] in
/-- The raw symbol codes of each arity form a primitive recursive relation. -/
private theorem primrecRel_isRelCode :
    PrimrecRel fun r k => ∃ R : Σ l, L.Relations l, encode R = r ∧ R.1 = k := by
  obtain ⟨l, -, hl⟩ := Finite.exists_univ_list (Σ l, L.Relations l)
  refine (PrimrecRel.exists_mem_list (R := fun (a : ℕ × ℕ) (b : ℕ × ℕ) => a = b)
    Primrec.eq).comp (Primrec.const (l.map fun R => (encode R, R.1))) Primrec.id |>.of_eq ?_
  · intro p
    constructor
    · rintro ⟨_, hm, rfl⟩
      obtain ⟨R, -, rfl⟩ := List.mem_map.1 hm
      exact ⟨R, rfl, rfl⟩
    · rintro ⟨R, h1, h2⟩
      exact ⟨_, List.mem_map.2 ⟨R, hl R, rfl⟩, Prod.ext h1 h2⟩

/-- **The raw coding of bounded formulas**: `φ` is coded by the code of `toRaw φ`. It is a
definition, available as an instance after
`open scoped FirstOrder.Language.BoundedFormula.RawCoding`; see the module documentation for why it
is not a global instance. -/
@[instance_reducible]
def primcodableRaw : Primcodable (L.BoundedFormula α n) :=
  letI := encodableRaw (L := L) (α := α) (n := n)
  { prim := by
      classical
      have hw : PrimrecPred fun m : ℕ => RawFormula.WellScoped (· ∈ Set.range (encode : α → ℕ))
          (fun r k => ∃ R : Σ l, L.Relations l, encode R = r ∧ R.1 = k) n
          (Denumerable.ofNat RawFormula m) :=
        (RawFormula.primrecRel_wellScoped Primcodable.mem_range_encode primrecRel_isRelCode).comp
          (Primrec.const n) (Primrec.ofNat RawFormula)
      refine Primrec.nat_iff.1 ((Primrec.ite hw Primrec.succ (Primrec.const 0)).of_eq fun m => ?_)
      change _ = encode ((decode m : Option RawFormula).bind (fromRaw n))
      rw [Denumerable.decode_eq_ofNat, Option.bind_some]
      split_ifs with h
      · obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.1 (isSome_fromRaw.2 h)
        rw [hφ, encode_some]
        change _ = encode φ.toRaw + 1
        rw [toRaw_of_fromRaw hφ, Denumerable.encode_ofNat]
      · rw [Option.not_isSome_iff_eq_none.1 (mt isSome_fromRaw.1 h)]
        rfl }

namespace RawCoding

/-- The raw coding as a scoped instance. -/
scoped instance instPrimcodable : Primcodable (L.BoundedFormula α n) := primcodableRaw

end RawCoding

open scoped RawCoding

theorem encode_eq_encode_toRaw (φ : L.BoundedFormula α n) : encode φ = encode φ.toRaw := by
  rfl

/-- A function into bounded formulas is primitive recursive iff its raw formulas are. -/
theorem primrec_iff_primrec_toRaw {β : Type*} [Primcodable β] {f : β → L.BoundedFormula α n} :
    Primrec f ↔ Primrec fun b => (f b).toRaw :=
  Primrec.encode_iff.symm.trans <| by
    simp only [encode_eq_encode_toRaw]
    exact Primrec.encode_iff

theorem primrec_toRaw : Primrec (toRaw : L.BoundedFormula α n → RawFormula) :=
  primrec_iff_primrec_toRaw.1 Primrec.id

theorem primrec_fromRaw : Primrec (fromRaw (L := L) (α := α) n) := by
  refine (Primrec.decode (α := L.BoundedFormula α n)).comp Primrec.encode |>.of_eq fun χ => ?_
  change (decode (encode χ) : Option RawFormula).bind (fromRaw n) = _
  rw [encodek, Option.bind_some]

theorem primrec_imp : Primrec₂ (imp : L.BoundedFormula α n → _ → _) :=
  primrec_iff_primrec_toRaw.2 (RawFormula.primrec_imp (primrec_toRaw.comp Primrec.fst)
    (primrec_toRaw.comp Primrec.snd))

theorem primrec_all : Primrec (all : L.BoundedFormula α (n + 1) → L.BoundedFormula α n) :=
  primrec_iff_primrec_toRaw.2 (RawFormula.primrec_all (Primrec.const _) primrec_toRaw)

theorem primrec_not : Primrec (BoundedFormula.not : L.BoundedFormula α n → _) :=
  primrec_iff_primrec_toRaw.2 (RawFormula.primrec_neg primrec_toRaw)

theorem primrec_ex : Primrec (BoundedFormula.ex : L.BoundedFormula α (n + 1) → _) :=
  primrec_not.comp (primrec_all.comp primrec_not)

theorem primrec_rawVar : Primrec (rawVar : α ⊕ Fin n → ℕ) :=
  (Primrec.sumCasesOn Primrec.id
    (Primrec.nat_double_succ.comp (Primrec.encode.comp Primrec.snd)).to₂
    (Primrec.nat_double.comp (Primrec.fin_val.comp Primrec.snd)).to₂).of_eq fun v => by
    rcases v with a | i <;> rfl

/-- A relation symbol applied to a tuple of variables is primitive recursive in the tuple. -/
theorem primrec_rel {l : ℕ} (R : L.Relations l) :
    Primrec fun vs : Fin l → α ⊕ Fin n => rel (α := α) R fun i => .var (vs i) :=
  primrec_iff_primrec_toRaw.2 (RawFormula.primrec_rel (Primrec.const _)
    (Primrec.list_ofFn fun i => primrec_rawVar.comp (Primrec.fin_app.comp Primrec.id
      (Primrec.const i))))

/-- Equality of two variables is primitive recursive in the variables. -/
theorem primrec_equal :
    Primrec₂ fun v w : α ⊕ Fin n => (equal (.var v) (.var w) : L.BoundedFormula α n) :=
  primrec_iff_primrec_toRaw.2 (RawFormula.primrec_equal (primrec_rawVar.comp Primrec.fst)
    (primrec_rawVar.comp Primrec.snd))

/-- Quantifier rank is primitive recursive under the raw coding. -/
theorem primrec_quantifierRank : Primrec (quantifierRank : L.BoundedFormula α n → ℕ) :=
  (RawFormula.primrec_quantifierDepth.comp primrec_toRaw).of_eq quantifierDepth_toRaw

end Coding

/-! ### Independence of the symbol encoding -/

section SymbolEncoding

variable [Primcodable α] [Finite (Σ l, L.Relations l)] [L.IsRelational]

/-- Changing the encoding of the symbols renames the raw symbol codes through the finite table
`σ`. -/
private theorem toRaw_eq_rename (e₁ e₂ : Encodable (Σ l, L.Relations l)) :
    ∃ σ : List ℕ, ∀ φ : L.BoundedFormula α n,
      @toRaw L α _ e₂ _ n φ = RawFormula.rename σ (@toRaw L α _ e₁ _ n φ) := by
  obtain ⟨l, -, hl⟩ := Finite.exists_univ_list (Σ l, L.Relations l)
  let B := (l.map fun R => @encode _ e₁ R).foldr max 0 + 1
  let σ := (List.range B).map fun r => ((@decode₂ _ e₁ r).map fun R => @encode _ e₂ R).getD r
  have hB : ∀ R, @encode _ e₁ R < B := fun R => Nat.lt_succ_of_le
    (List.le_max_of_le' 0 (List.mem_map.2 ⟨R, hl R, rfl⟩) le_rfl)
  have hσ : ∀ R, σ.getD (@encode _ e₁ R) (@encode _ e₁ R) = @encode _ e₂ R := by
    intro R
    rw [List.getD_eq_getElem?_getD]
    simp [σ, hB R, @encodek₂ _ e₁]
  refine ⟨σ, fun φ => ?_⟩
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel R ts => simp only [toRaw_rel, RawFormula.rename, hσ]
  | imp φ ψ ihφ ihψ => simp only [toRaw_imp, RawFormula.rename, ihφ, ihψ]
  | all φ ih => simp only [toRaw_all, RawFormula.rename, ih]

/-- **The raw coding does not depend on the symbol encoding**: for two encodings `e₁`, `e₂` of the
relation symbols, the identity is primitive recursive from the coding induced by `e₁` to the one
induced by `e₂`. -/
theorem primrec_id_primcodableRaw (e₁ e₂ : Encodable (Σ l, L.Relations l)) :
    @Primrec _ _ (@primcodableRaw L α n _ e₁ _ _) (@primcodableRaw L α n _ e₂ _ _) id := by
  let _ := e₁
  obtain ⟨σ, hσ⟩ := toRaw_eq_rename (L := L) (α := α) (n := n) e₁ e₂
  let _ : Primcodable (L.BoundedFormula α n) := primcodableRaw
  refine @Primrec.encode_iff _ _ _ (@primcodableRaw L α n _ e₂ _ _) _ |>.1 ?_
  change Primrec fun φ : L.BoundedFormula α n => encode (@toRaw L α _ e₂ _ n φ)
  simp only [hσ]
  exact Primrec.encode.comp (RawFormula.primrec₂_rename.comp (Primrec.const σ) primrec_toRaw)

end SymbolEncoding

/-! ### Semantics -/

section Semantics

variable [Encodable α] [Encodable (Σ l, L.Relations l)] [L.IsRelational]
variable {M : Type*} [L.Structure M]

omit [Encodable (Σ l, L.Relations l)] in
private theorem rawTerm_realize {ρ : ℕ → M} {v : α → M} {xs : Fin n → M}
    (hρ : ∀ w, ρ (rawVar w) = Sum.elim v xs w) (t : L.Term (α ⊕ Fin n)) :
    ρ (rawTerm t) = t.realize (Sum.elim v xs) := by
  obtain ⟨w, rfl⟩ := term_eq_var t
  simp [hρ]

/-- **The translation preserves meaning.** Under a raw interpretation `I` that interprets the code
of each relation symbol as the symbol, and an assignment `ρ` that gives the raw name of each
variable its value, `toRaw φ` holds iff `φ` does. -/
theorem realize_toRaw {I : ℕ → List M → Prop}
    (hI : ∀ {l} (R : L.Relations l) (xs : Fin l → M),
      I (encode (⟨l, R⟩ : Σ l, L.Relations l)) (List.ofFn xs) ↔ Structure.RelMap R xs) :
    ∀ {n} (φ : L.BoundedFormula α n) {ρ : ℕ → M} {v : α → M} {xs : Fin n → M},
      (∀ w, ρ (rawVar w) = Sum.elim v xs w) → (φ.toRaw.Realize I ρ ↔ φ.Realize v xs)
  | _, falsum, _, _, _, _ => Iff.rfl
  | _, equal t₁ t₂, ρ, v, xs, hρ => by
    rw [toRaw_equal, RawFormula.realize_equal, rawTerm_realize hρ, rawTerm_realize hρ]
    rfl
  | _, rel R ts, ρ, v, xs, hρ => by
    rw [toRaw_rel, RawFormula.realize_rel, List.map_ofFn]
    simp only [Function.comp_def, rawTerm_realize hρ]
    exact hI R _
  | _, imp φ ψ, ρ, v, xs, hρ => by
    simp only [toRaw_imp, RawFormula.realize_imp, realize_toRaw hI φ hρ, realize_toRaw hI ψ hρ]
    rfl
  | k, all φ, ρ, v, xs, hρ => by
    simp only [toRaw_all, RawFormula.realize_all]
    refine forall_congr' fun m => realize_toRaw hI φ fun w => ?_
    rcases w with a | i
    · rw [Function.update_of_ne (by simp; omega)]
      simpa using hρ (.inl a)
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · rw [Function.update_of_ne (by simp; omega)]
        simpa using hρ (.inr j)

end Semantics

end BoundedFormula

/-! ### Finite satisfiability and finite validity of sentences -/

namespace Sentence

/-- A sentence is **finitely satisfiable** when it holds in some finite nonempty structure. The
structure's carrier ranges over `Type`, which loses nothing since every finite structure has an
isomorphic copy on some `Fin n`. This is not Mathlib's
`FirstOrder.Language.Theory.IsFinitelySatisfiable`, which asks that every finite subset of a theory
have some (possibly infinite) model. -/
@[expose]
def FinSat (φ : L.Sentence) : Prop :=
  ∃ (M : Type) (_ : L.Structure M) (_ : Finite M) (_ : Nonempty M), M ⊨ φ

/-- A sentence is **finitely valid** when it holds in every finite nonempty structure whose
carrier is in `Type`. -/
@[expose]
def FinValid (φ : L.Sentence) : Prop :=
  ∀ (M : Type) [L.Structure M] [Finite M] [Nonempty M], M ⊨ φ

theorem finValid_not_iff (φ : L.Sentence) : FinValid φ.not ↔ ¬FinSat φ := by
  simp only [FinValid, FinSat, realize_not, not_exists]

theorem finValid_iff_not_finSat_not (φ : L.Sentence) : FinValid φ ↔ ¬FinSat φ.not := by
  simp only [FinValid, FinSat, realize_not, not_exists, not_not]

variable [Encodable (Σ l, L.Relations l)] [L.IsRelational]

open BoundedFormula

/-- A sentence holds in some `L`-structure on a nonempty type `M` iff its raw formula holds on `M`
under some raw interpretation and assignment. -/
theorem exists_structure_realize_iff_toRaw (M : Type*) [Nonempty M] (φ : L.Sentence) :
    (∃ _ : L.Structure M, M ⊨ φ) ↔
      ∃ (I : ℕ → List M → Prop) (ρ : ℕ → M), φ.toRaw.Realize I ρ := by
  constructor
  · rintro ⟨_, h⟩
    obtain ⟨m⟩ := ‹Nonempty M›
    let I : ℕ → List M → Prop := fun r as =>
      ∃ (l : ℕ) (R : L.Relations l) (xs : Fin l → M),
        encode (⟨l, R⟩ : Σ l, L.Relations l) = r ∧ List.ofFn xs = as ∧ Structure.RelMap R xs
    have hI : ∀ {l} (R : L.Relations l) (xs : Fin l → M),
        I (encode (⟨l, R⟩ : Σ l, L.Relations l)) (List.ofFn xs) ↔ Structure.RelMap R xs := by
      intro l R xs
      constructor
      · rintro ⟨l', R', xs', he, hx, hR⟩
        obtain ⟨rfl, hR'⟩ := Sigma.mk.inj_iff.1 (encode_injective he)
        obtain rfl := eq_of_heq hR'
        rw [List.ofFn_inj] at hx
        rwa [← hx]
      · exact fun h => ⟨l, R, xs, rfl, rfl, h⟩
    refine ⟨I, fun _ => m, (realize_toRaw hI φ fun w => ?_).2 h⟩
    rcases w with a | i
    · exact a.elim
    · exact i.elim0
  · rintro ⟨I, ρ, h⟩
    let _ : L.Structure M :=
      { RelMap := fun {l} R xs => I (encode (⟨l, R⟩ : Σ l, L.Relations l)) (List.ofFn xs) }
    refine ⟨inferInstance, (realize_toRaw (fun R xs => Iff.rfl) φ fun w => ?_).1 h⟩
    rcases w with a | i
    · exact a.elim
    · exact i.elim0

/-- A sentence is finitely satisfiable iff its raw formula is. -/
theorem finSat_iff_toRaw (φ : L.Sentence) : FinSat φ ↔ RawFormula.FinSat (toRaw φ) := by
  constructor
  · rintro ⟨M, hS, hf, hn, h⟩
    obtain ⟨I, ρ, h'⟩ := (exists_structure_realize_iff_toRaw M φ).1 ⟨hS, h⟩
    exact ⟨M, hf, hn, I, ρ, h'⟩
  · rintro ⟨M, hf, hn, I, ρ, h⟩
    obtain ⟨hS, h'⟩ := (exists_structure_realize_iff_toRaw M φ).2 ⟨I, ρ, h⟩
    exact ⟨M, hS, hf, hn, h'⟩

/-- A sentence is finitely valid iff its raw formula is. -/
theorem finValid_iff_toRaw (φ : L.Sentence) : FinValid φ ↔ RawFormula.FinValid (toRaw φ) := by
  rw [finValid_iff_not_finSat_not, finSat_iff_toRaw, toRaw_not,
    RawFormula.finValid_iff_not_finSat_neg]

end Sentence

end FirstOrder.Language
