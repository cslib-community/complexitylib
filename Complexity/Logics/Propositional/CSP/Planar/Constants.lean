/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Planar.Construction
import Complexity.Logics.Propositional.CSP.Planar.NonSelfDual
import Mathlib.Tactic.FinCases

/-!
# Constants and disequality from ordered constructions

This is the semantic descent of [DvorakKupec2015], Lemma 3, printed pp. 437–438.
Equality restriction is always followed immediately by deletion of the first of the adjacent
ports, so minimum arity suffices. Unary constant operations are kept distinct from unary pin
relations. Different language symbols may witness the failures of the different polymorphisms.

The conclusions give finite `RelationMinor.Construction` trees, with all enabling relations
constructed from original symbols. Geometric interpretation and complexity are not claimed.

## Main results

* `Cslib.Logic.PL.CSP.RelationMinor.disequality_of_not_hasSchaeferPolymorphism`: disequality.
* `Cslib.Logic.PL.CSP.RelationMinor.constants_of_not_hasSchaeferPolymorphism`: both pins as well.
-/

public section

namespace Cslib.Logic.PL.CSP.RelationMinor

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool} {m n : ℕ}

private theorem minimal_available (P : ∀ n, Set (Fin n → Bool) → Prop)
    {R : Set (Fin m → Bool)} (hR : Available arity sem R) (hp : P m R) :
    ∃ (n : ℕ) (S : Set (Fin n → Bool)), Available arity sem S ∧ P n S ∧
      ∀ (k : ℕ) (T : Set (Fin k → Bool)), Available arity sem T → k < n → ¬P k T := by
  classical
  let Q (n : ℕ) := ∃ S : Set (Fin n → Bool), Available arity sem S ∧ P n S
  have hex : ∃ n, Q n := ⟨m, R, hR, hp⟩
  obtain ⟨S, hc, hs⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, S, hc, hs, ?_⟩
  intro k T hT hlt hp
  exact (Nat.find_min hex hlt) ⟨T, hT, hp⟩

private def spike (b : Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !b else b

private theorem mem_adjacent {R : Set (Fin (n + 2) → Bool)} {a : Fin (n + 2) → Bool}
    (ha : a ∈ R) (d : Bool) (he : a 0 = (a 1 ^^ d)) : Fin.tail a ∈ adjacent R d := by
  change Fin.cons (a 1 ^^ d) (Fin.tail a) ∈ R
  rw [← he, Fin.cons_self_tail]
  exact ha

private theorem constant_not_mem_adjacent {R : Set (Fin (n + 2) → Bool)} (b : Bool)
    (hz : (fun _ => b) ∉ R) : (fun _ => b) ∉ adjacent R false := by
  intro h
  apply hz
  change Fin.cons (b ^^ false) (fun _ => b) ∈ R at h
  have heq : (Fin.cons (b ^^ false) (fun _ => b) : Fin (n + 2) → Bool) = fun _ => b := by
    ext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp
  exact heq ▸ h

private theorem spike_mem {R : Set (Fin (n + 1) → Bool)} (b : Bool)
    (hz : (fun _ => b) ∉ R) (j : Fin (n + 1))
    (hp : (fun _ => b) ∈ project R j) : spike b j ∈ R := by
  obtain ⟨v, hv⟩ := hp
  have hvb : v ≠ b := by
    intro heq
    subst v
    apply hz
    convert hv using 1
    ext i
    rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩ <;> simp
  have heq : (j.insertNth v (fun _ : Fin n => b) : Fin (n + 1) → Bool) = spike b j := by
    ext i
    rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
    · simp only [Fin.insertNth_apply_same, spike, ite_true]
      cases v <;> cases b <;> simp_all
    · simp [spike, Fin.succAbove_ne]
  exact heq ▸ hv

/-- Failure of a unary constant yields disequality or the opposite unary pin, by projections
and immediate adjacent equality-deletions alone. This includes arbitrary and nullary arities. -/
theorem disequality_or_pin_of_missing_constant {R : Set (Fin m → Bool)}
    (hR : Available arity sem R) (b : Bool) (hne : R.Nonempty)
    (hz : (fun _ => b) ∉ R) :
    Available arity sem disequality ∨ Available arity sem (pin (!b)) := by
  obtain ⟨n, S, ⟨c⟩, ⟨⟨a, ha⟩, hz⟩, hmin⟩ :=
    minimal_available (fun n S => S.Nonempty ∧ (fun _ : Fin n => b) ∉ S) hR ⟨hne, hz⟩
  have hn : n ≠ 0 := by
    intro heq
    subst n
    exact hz ((Subsingleton.elim a (fun _ => b)) ▸ ha)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hp (j : Fin (n + 1)) : (fun _ => b) ∈ project S j := by
    by_contra hh
    exact hmin n _ ⟨.project c j⟩ (by omega)
      ⟨⟨j.removeNth a, remove_mem_project ha j⟩, hh⟩
  have hu (j : Fin (n + 1)) : spike b j ∈ S := spike_mem b hz j (hp j)
  have hn2 : n + 1 ≤ 2 := by
    by_contra hh
    have hn3 : 3 ≤ n + 1 := by omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hw : (adjacent S false).Nonempty := by
      refine ⟨Fin.tail (spike b (⟨2, by omega⟩ : Fin (k + 2 + 1))), ?_⟩
      exact mem_adjacent (hu _) false (by simp [spike])
    exact hmin (k + 2) _ ⟨.equalDrop c⟩ (by omega)
      ⟨hw, constant_not_mem_adjacent b hz⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst n
    have rows (x : Fin 1 → Bool) : x = (fun _ => b) ∨ x = fun _ => !b := by
      cases b <;> revert x <;> decide
    have ha' : a = fun _ => !b := (rows a).resolve_left (fun heq => hz (heq ▸ ha))
    have heq : S = pin (!b) := by
      ext x
      rcases rows x with rfl | rfl
      · simp [pin, hz]
      · simp [pin, show (fun _ : Fin 1 => !b) ∈ S from ha' ▸ ha]
    exact .inr ⟨heq ▸ c⟩
  · have hn1 : n = 1 := by omega
    subst n
    have hlast : (fun _ : Fin 2 => !b) ∉ S := by
      intro h
      have hw : (adjacent S false).Nonempty :=
        ⟨_, mem_adjacent h false (by simp)⟩
      exact hmin 1 _ ⟨.equalDrop c⟩ (by omega)
        ⟨hw, constant_not_mem_adjacent b hz⟩
    have rows (x : Fin 2 → Bool) : x = (fun _ => b) ∨ x = spike b 0 ∨
        x = spike b 1 ∨ x = fun _ => !b := by cases b <;> revert x <;> decide
    have heq : S = disequality := by
      ext x
      rcases rows x with rfl | rfl | rfl | rfl <;> simp [disequality, hz, hlast, hu, spike]
    exact .inl ⟨heq ▸ c⟩

private theorem binary_minor_of_failure {R : Set (Fin m → Bool)}
    (hR : Available arity sem R) (pins : ∀ b, Available arity sem (pin b))
    (b : Bool) (f : (Fin 2 → Bool) → Bool)
    (hid : ∀ d, f (fun _ => d) = d)
    (hdiff : ∀ a, a 0 ≠ a 1 → f a = b)
    (h : ¬IsPolymorphism f R) :
    ∃ S : Set (Fin 2 → Bool), Available arity sem S ∧
      disequality ⊆ S ∧ (fun _ => b) ∉ S := by
  classical
  obtain ⟨n, S, ⟨c⟩, hb, hmin⟩ :=
    minimal_available (fun _ S => ¬IsPolymorphism f S) hR h
  have hn : n ≠ 0 := by
    intro heq
    subst n
    apply hb
    intro a ha
    have heq : a 0 = (fun i => f (fun j => a j i)) := Subsingleton.elim _ _
    exact heq ▸ ha 0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have bad_pair (z : Fin 2 → Fin (n + 1) → Bool) (hz : ∀ q, z q ∈ S)
      (hout : (fun i => f (fun q => z q i)) ∉ S) (j : Fin (n + 1)) :
      z 0 j ≠ z 1 j := by
    intro heq
    have hc : IsPolymorphism f (cofactor S j (z 0 j)) := by
      by_contra hh
      exact hmin n _ ⟨.cofactor c j _ (Classical.choice (pins _))⟩ (by omega) hh
    apply hout
    apply mem_of_cofactor_closure (hid _) hc z hz
    intro q
    fin_cases q
    · rfl
    · exact heq.symm
  obtain ⟨a, ha, hout⟩ : ∃ a : Fin 2 → Fin (n + 1) → Bool,
      (∀ q, a q ∈ S) ∧ (fun i => f (fun q => a q i)) ∉ S := by
    simpa only [IsPolymorphism, not_forall, exists_prop] using hb
  have heout : (fun i => f (fun q => a q i)) = fun _ => b := by
    ext i
    exact hdiff _ (bad_pair a ha hout i)
  have hz : (fun _ : Fin (n + 1) => b) ∉ S := heout ▸ hout
  have hu (j : Fin (n + 1)) : spike b j ∈ S := by
    apply spike_mem b hz j
    have hp : IsPolymorphism f (project S j) := by
      by_contra hh
      exact hmin n _ ⟨.project c j⟩ (by omega) hh
    have hm := hp (fun q => j.removeNth (a q)) (fun q => remove_mem_project (ha q) j)
    have heq : (fun i => f (fun q => j.removeNth (a q) i)) = fun _ : Fin n => b :=
      congrArg j.removeNth heout
    exact heq ▸ hm
  have hn2 : 2 ≤ n + 1 := by
    by_contra hh
    have hn0 : n = 0 := by omega
    subst n
    have heq (q : Fin 2) : a q = fun _ => !b := by
      have rows (x : Fin 1 → Bool) : x = (fun _ => b) ∨ x = fun _ => !b := by
        cases b <;> revert x <;> decide
      exact (rows (a q)).resolve_left (fun heq => hz (heq ▸ ha q))
    exact bad_pair a ha hout 0 (by rw [heq 0, heq 1])
  have hnle : n + 1 ≤ 2 := by
    by_contra hh
    have hn3 : 3 ≤ n + 1 := by omega
    let i : Fin (n + 1) := ⟨0, by omega⟩
    let j : Fin (n + 1) := ⟨1, by omega⟩
    let k : Fin (n + 1) := ⟨2, by omega⟩
    let z : Fin 2 → Fin (n + 1) → Bool := ![spike b i, spike b j]
    have hzmem (q : Fin 2) : z q ∈ S := by fin_cases q <;> exact hu _
    have hez : (fun p => f (fun q => z q p)) = fun _ => b := by
      ext p
      by_cases hi : p = i
      · apply hdiff
        simp [z, spike, hi, i, j]
      · by_cases hj : p = j
        · apply hdiff
          simp [z, spike, hj, i, j]
        · have hconst : (fun q => z q p) = fun _ => b := by
            ext q
            fin_cases q <;> simp [z, spike, hi, hj]
          rw [hconst, hid]
    have hb' : (fun p => f (fun q => z q p)) ∉ S := hez.symm ▸ hz
    exact bad_pair z hzmem hb' k (by simp [z, spike, i, j, k])
  have hn1 : n = 1 := by omega
  subst n
  refine ⟨S, ⟨c⟩, ?_, hz⟩
  intro x hx
  have rows : x = spike b 0 ∨ x = spike b 1 := by
    have check : ∀ b (x : Fin 2 → Bool), x 0 ≠ x 1 →
        x = spike b 0 ∨ x = spike b 1 := by decide
    exact check b x hx
  rcases rows with rfl | rfl <;> exact hu _

/-- With actual unary pins, separate AND and OR failures construct disequality by the
specific binary intersection of Lemma 3. No ternary or unrestricted intersection is used. -/
theorem disequality_of_pins {R : Set (Fin m → Bool)} {S : Set (Fin n → Bool)}
    (hR : Available arity sem R) (hS : Available arity sem S)
    (pins : ∀ b, Available arity sem (pin b))
    (ha : ¬IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1) R)
    (ho : ¬IsPolymorphism (fun a : Fin 2 → Bool => a 0 || a 1) S) :
    Available arity sem disequality := by
  obtain ⟨P, ⟨p⟩, hinP, hzP⟩ := binary_minor_of_failure hR pins false
    (fun a => a 0 && a 1) (by intro b; cases b <;> rfl)
    (by intro a h; cases h0 : a 0 <;> cases h1 : a 1 <;> simp_all) ha
  obtain ⟨Q, ⟨q⟩, hinQ, hzQ⟩ := binary_minor_of_failure hS pins true
    (fun a => a 0 || a 1) (by intro b; cases b <;> rfl)
    (by intro a h; cases h0 : a 0 <;> cases h1 : a 1 <;> simp_all) ho
  have heq : P ∩ Q = disequality := by
    ext x
    constructor
    · rintro ⟨hp, hq⟩ he
      have hconst : x = fun _ => x 0 := by
        ext i
        fin_cases i
        · rfl
        · exact he.symm
      cases hb : x 0
      · have hxf : x = fun _ => false := hconst.trans (funext fun _ => hb)
        exact hzP (hxf ▸ hp)
      · have hxt : x = fun _ => true := hconst.trans (funext fun _ => hb)
        exact hzQ (hxt ▸ hq)
    · intro hx
      exact ⟨hinP hx, hinQ hx⟩
  exact ⟨heq ▸ Construction.binaryMeet p q⟩

/-- Disequality and failure of complement construct both unary pins. Each descent uses only
the first adjacent pair, with its first coordinate immediately deleted. -/
theorem pins_of_disequality {R : Set (Fin m → Bool)}
    (hR : Available arity sem R) (hd : Available arity sem disequality)
    (h : ¬IsPolymorphism (fun a : Fin 1 → Bool => !(a 0)) R) :
    ∀ b, Available arity sem (pin b) := by
  classical
  obtain ⟨n, S, ⟨c⟩, hb, hmin⟩ := minimal_available
    (fun _ S => ¬IsPolymorphism (fun a : Fin 1 → Bool => !(a 0)) S) hR h
  obtain ⟨a, ha, hout⟩ : ∃ a : Fin 1 → Fin n → Bool,
      (∀ q, a q ∈ S) ∧ (fun i => !(a 0 i)) ∉ S := by
    simpa only [IsPolymorphism, not_forall, exists_prop] using hb
  let x := a 0
  have hx : x ∈ S := ha 0
  have hnot : (fun i => !(x i)) ∉ S := hout
  have hn : n ≠ 0 := by
    intro heq
    subst n
    exact hnot ((Subsingleton.elim x (fun i => !(x i))) ▸ hx)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hn0 : n = 0 := by
    by_contra hh
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh
    let d := x 0 ^^ x 1
    have hcond : x 0 = (x 1 ^^ d) := by
      dsimp [d]
      cases x 0 <;> cases x 1 <;> rfl
    have hc : Available arity sem (adjacent S d) := by
      cases he : d
      · exact ⟨.equalDrop c⟩
      · exact ⟨.differentDrop c (Classical.choice hd)⟩
    have hm := mem_adjacent hx d hcond
    have hf : ¬IsPolymorphism (fun a : Fin 1 → Bool => !(a 0)) (adjacent S d) := by
      intro hf
      have hh := hf (fun _ => Fin.tail x) (fun _ => hm)
      apply hnot
      change Fin.cons (!(x 1) ^^ d) (Fin.tail (fun i => !(x i))) ∈ S at hh
      have hcond' : (!(x 0)) = (!(x 1) ^^ d) := by
        dsimp [d]
        cases x 0 <;> cases x 1 <;> rfl
      rwa [← hcond', Fin.cons_self_tail (fun i => !(x i))] at hh
    exact hmin (k + 1) _ hc (by omega) hf
  subst n
  have heq : S = pin (x 0) := by
    have rows (y : Fin 1 → Bool) : y = x ∨ y = fun i => !(x i) := by
      have check : ∀ (x y : Fin 1 → Bool), y = x ∨ y = fun i => !(x i) := by decide
      exact check x y
    ext y
    rcases rows y with rfl | rfl <;> simp [pin, hx, hnot]
  have hp : Construction arity sem (pin (x 0)) := heq ▸ c
  have htwist : twist (pin (x 0)) (Pi.single 0 true) = pin (!(x 0)) := by
    ext y
    change (y 0 + true) = x 0 ↔ y 0 = !(x 0)
    cases y 0 <;> cases x 0 <;> decide
  have hq : Construction arity sem (pin (!(x 0))) :=
    htwist ▸ Construction.flip hp 0 (Classical.choice hd)
  intro b
  have hb : b = x 0 ∨ b = !(x 0) := by cases b <;> cases x 0 <;> simp
  rcases hb with rfl | rfl
  · exact ⟨hp⟩
  · exact ⟨hq⟩

/-- The non-Schaefer hypothesis constructs disequality from original language symbols.
The ZERO/ONE witnesses and the AND/OR witnesses are selected independently. -/
theorem disequality_of_not_hasSchaeferPolymorphism
    (h : ¬HasSchaeferPolymorphism arity sem) : Available arity sem disequality := by
  classical
  have hzero : ¬HasPolymorphism arity sem (fun _ : Fin 1 → Bool => false) :=
    fun hz => h (.inl hz)
  have hone : ¬HasPolymorphism arity sem (fun _ : Fin 1 → Bool => true) :=
    fun ho => h (.inr (.inl ho))
  rw [hasPolymorphism_const_iff] at hzero hone
  simp only [not_forall] at hzero hone
  obtain ⟨r, hr, hz⟩ := hzero
  obtain ⟨s, hs, ho⟩ := hone
  rcases disequality_or_pin_of_missing_constant ⟨.atom r⟩ false hr hz with hd | h1
  · exact hd
  rcases disequality_or_pin_of_missing_constant ⟨.atom s⟩ true hs ho with hd | h0
  · exact hd
  have pins (b : Bool) : Available arity sem (pin b) := by
    cases b
    · exact h0
    · exact h1
  have hand : ¬HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 && a 1) :=
    fun ha => h (.inr (.inr (.inl ha)))
  have hor : ¬HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 || a 1) :=
    fun ho => h (.inr (.inr (.inr (.inl ho))))
  simp only [HasPolymorphism, not_forall] at hand hor
  obtain ⟨r, hr⟩ := hand
  obtain ⟨s, hs⟩ := hor
  exact disequality_of_pins ⟨.atom r⟩ ⟨.atom s⟩ pins hr hs

/-- Lemma 3's nonselfdual endpoint, with no adjoined-constant premise: disequality and both
unary pins have finite ordered constructions from the original language. Complement, constant,
AND and OR failures may belong to different symbols. -/
theorem constants_of_not_hasSchaeferPolymorphism
    (h : ¬HasSchaeferPolymorphism arity sem)
    (hn : ¬HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0))) :
    Available arity sem disequality ∧ ∀ b, Available arity sem (pin b) := by
  classical
  have hd := disequality_of_not_hasSchaeferPolymorphism h
  simp only [HasPolymorphism, not_forall] at hn
  obtain ⟨r, hr⟩ := hn
  exact ⟨hd, pins_of_disequality ⟨.atom r⟩ hd hr⟩

end Cslib.Logic.PL.CSP.RelationMinor
