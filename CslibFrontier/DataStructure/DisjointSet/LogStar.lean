import CslibFrontier.Init
import CslibFrontier.DataStructure.DisjointSet.UnionFind
import CslibFrontier.DataStructure.StateTransition.Amortized
import CslibFrontier.Foundations.Data.Nat.LogStar

namespace Cslib.DataStructure.DisjointSet.UnionFind

@[expose] def RankCount (uf : Batteries.UnionFind) : Prop :=
  ∀ ⦃r a : ℕ⦄, r < uf.size → uf.parent r = r →
    2 ^ a * ((equivClass uf r).filter (fun x => a ≤ uf.rank x)).card ≤ 2 * (equivClass uf r).card

namespace RankCount

private theorem unionFind_ext {u v : Batteries.UnionFind} (h : u.arr = v.arr) : u = v := by
  cases u; cases v; cases h; rfl

private theorem rank_link (uf : Batteries.UnionFind) (x y : Fin uf.size)
    (hy : uf.parent y.1 = y.1) (i : ℕ) :
    (uf.link x y hy).rank i =
      if x.1 ≠ y.1 ∧ uf.rank x.1 = uf.rank y.1 ∧ y.1 = i then
        uf.rank y.1 + 1
      else
        uf.rank i := by
  simp only [Batteries.UnionFind.rank, Batteries.UnionFind.arr_link, Batteries.UnionFind.linkAux]
  by_cases hxy : x.1 = y.1
  · simp [hxy]
  · simp only [hxy, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    have hrx : Batteries.UnionFind.rankD uf.arr x.1 = uf.arr[x.1].rank :=
      Batteries.UnionFind.rankD_eq x.2
    have hry : Batteries.UnionFind.rankD uf.arr y.1 = uf.arr[y.1].rank :=
      Batteries.UnionFind.rankD_eq y.2
    rw [hrx, hry]
    by_cases hlt : uf.arr[y.1].rank < uf.arr[x.1].rank
    · have hne_rk : uf.arr[x.1].rank ≠ uf.arr[y.1].rank := Nat.ne_of_gt hlt
      simp only [hlt, ↓reduceIte, hne_rk, false_and, Batteries.UnionFind.rankD_set]
      by_cases hyi : y.1 = i
      · subst hyi
        simp [hry]
      · simp [hyi]
    · simp only [hlt, ↓reduceIte]
      by_cases heq_rk : uf.arr[x.1].rank = uf.arr[y.1].rank
      · simp only [heq_rk, ↓reduceIte, true_and, Batteries.UnionFind.rankD_set]
        by_cases hyi : y.1 = i
        · simp [hyi]
        · simp only [hyi, ↓reduceIte]
          by_cases hxi : x.1 = i
          · subst hxi
            simp [heq_rk, hrx]
          · simp [hxi]
      · simp only [heq_rk, ↓reduceIte, false_and, Batteries.UnionFind.rankD_set]
        by_cases hxi : x.1 = i
        · subst hxi
          simp [hrx]
        · simp [hxi]

theorem link {uf : Batteries.UnionFind} (h : RankCount uf) (h_valid : ValidRank uf) {x y : Fin uf.size}
    (hx : uf.parent x.1 = x.1) (hy : uf.parent y.1 = y.1) :
    RankCount (uf.link x y hy) := by
  intro r a hr hp'
  have hsize : (uf.link x y hy).size = uf.size := by simp [Batteries.UnionFind.size]
  rw [hsize] at hr
  by_cases hxy : x.1 = y.1
  · have heq : uf.link x y hy = uf := by
      apply unionFind_ext
      simp [Batteries.UnionFind.linkAux, hxy]
    rw [heq] at hp' ⊢
    exact h hr hp'
  · obtain ⟨r₀, hr₀, hroot⟩ := Batteries.UnionFind.root_link hx hy
    have hx_rootD : uf.rootD x.1 = x.1 := Batteries.UnionFind.rootD_eq_self.mpr hx
    have hy_rootD : uf.rootD y.1 = y.1 := Batteries.UnionFind.rootD_eq_self.mpr hy
    have hr₀_eq : (uf.link x y hy).rootD x.1 = r₀.1 := by
      simpa [hx_rootD] using hroot x.1
    have hr₀_parent : (uf.link x y hy).parent r₀.1 = r₀.1 := by
      rw [← hr₀_eq]
      exact Batteries.UnionFind.parent_rootD _ _
    by_cases hlt : uf.rank y.1 < uf.rank x.1
    · have hparent : ∀ i, (uf.link x y hy).parent i = if y.1 = i then x.1 else uf.parent i := by
        intro i
        rw [Batteries.UnionFind.parent_link hy]
        have hxy_false : (x.1 = y.1) = False := eq_false hxy
        have hlt_true : (uf.rank y.1 < uf.rank x.1) = True := eq_true hlt
        simp only [hxy_false, hlt_true, ite_false, ite_true]
      have hy_not_root : (uf.link x y hy).parent y.1 ≠ y.1 := by
        rw [hparent y.1, ite_eq_left rfl]
        exact hxy
      have hr₀_x : r₀ = x := by
        rcases hr₀ with hrx | hry
        · exact hrx
        · rw [hry] at hr₀_parent
          exact absurd hr₀_parent hy_not_root
      rw [hr₀_x] at hroot
      have hyr : y.1 ≠ r := fun heq => by
        rw [← heq] at hp'
        exact hy_not_root hp'
      have hp : uf.parent r = r := by
        have hp₁ := hp'
        rw [hparent r, ite_eq_right hyr] at hp₁
        exact hp₁
      have hrank : ∀ i, (uf.link x y hy).rank i = uf.rank i := by
        intro i
        rw [rank_link]
        split
        · next hcond =>
          obtain ⟨_, heq_rk, hyr'⟩ := hcond
          exact absurd heq_rk (ne_of_gt hlt)
        · rfl
      have heq_class : equivClass (uf.link x y hy) r = if r = x.1 then equivClass uf x.1 ∪ equivClass uf y.1 else equivClass uf r := by
        ext i
        by_cases hxr : r = x.1
        · rw [ite_eq_left hxr, mem_equivClass, hsize, Finset.mem_union, mem_equivClass, mem_equivClass, hroot i]
          by_cases h_root : uf.rootD i = x.1 ∨ uf.rootD i = y.1
          · rw [ite_eq_left h_root]
            constructor
            · rintro ⟨hi, -⟩
              rcases h_root with h1 | h2
              · exact Or.inl ⟨hi, h1⟩
              · exact Or.inr ⟨hi, h2⟩
            · rintro (⟨hi, _⟩ | ⟨hi, _⟩)
              · exact ⟨hi, hxr.symm⟩
              · exact ⟨hi, hxr.symm⟩
          · rw [ite_eq_right h_root]
            constructor
            · rintro ⟨hi, heq⟩
              exact Or.inl ⟨hi, heq.trans hxr⟩
            · rintro (⟨hi, h1⟩ | ⟨hi, h2⟩)
              · exact absurd (Or.inl h1) h_root
              · exact absurd (Or.inr h2) h_root
        · rw [ite_eq_right hxr, mem_equivClass, hsize, mem_equivClass, hroot i]
          by_cases h_root : uf.rootD i = x.1 ∨ uf.rootD i = y.1
          · rw [ite_eq_left h_root]
            constructor
            · rintro ⟨hi, heq⟩
              exact absurd heq.symm hxr
            · rintro ⟨hi, heq⟩
              rcases h_root with h1 | h2
              · exact absurd (heq.symm.trans h1) hxr
              · exact absurd (h2.symm.trans heq) hyr
          · rw [ite_eq_right h_root]
      by_cases hxr : r = x.1
      · subst hxr
        rw [heq_class, ite_eq_left rfl]
        have h_filter_eq : ((equivClass uf x.1 ∪ equivClass uf y.1).filter (fun z => a ≤ (uf.link x y hy).rank z)) =
                           ((equivClass uf x.1).filter (fun z => a ≤ uf.rank z)) ∪
                           ((equivClass uf y.1).filter (fun z => a ≤ uf.rank z)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_union]
          rw [hrank i]
          constructor
          · rintro ⟨h1 | h2, h3⟩
            · exact Or.inl ⟨h1, h3⟩
            · exact Or.inr ⟨h2, h3⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨Or.inl h1, h2⟩
            · exact ⟨Or.inr h1, h2⟩
        rw [h_filter_eq]
        have h_disj : Disjoint (equivClass uf x.1) (equivClass uf y.1) := disjoint_equivClass_of_ne uf hxy
        have h_disj_filter : Disjoint ((equivClass uf x.1).filter (fun z => a ≤ uf.rank z)) ((equivClass uf y.1).filter (fun z => a ≤ uf.rank z)) :=
          Finset.disjoint_filter_filter h_disj
        rw [Finset.card_union_of_disjoint h_disj_filter, Finset.card_union_of_disjoint h_disj, Nat.mul_add, Nat.mul_add]
        have hp_x : uf.parent x.1 = x.1 := hx
        have h1 := h (a := a) hr hp_x
        have h2 := h (a := a) y.2 hy
        exact Nat.add_le_add h1 h2
      · rw [heq_class, ite_eq_right hxr]
        have h_filter_eq : ((equivClass uf r).filter (fun z => a ≤ (uf.link x y hy).rank z)) =
                           ((equivClass uf r).filter (fun z => a ≤ uf.rank z)) := by
          ext i
          simp only [Finset.mem_filter]
          rw [hrank i]
        rw [h_filter_eq]
        exact h hr hp
    · by_cases hlt_y : uf.rank x.1 < uf.rank y.1
      · have hparent : ∀ i, (uf.link x y hy).parent i = if x.1 = i then y.1 else uf.parent i := by
          intro i
          rw [Batteries.UnionFind.parent_link hy]
          have hxy_false : (x.1 = y.1) = False := eq_false hxy
          have hlt_false : (uf.rank y.1 < uf.rank x.1) = False := eq_false hlt
          simp only [hxy_false, hlt_false, ite_false]
        have hx_not_root : (uf.link x y hy).parent x.1 ≠ x.1 := by
          rw [hparent x.1, ite_eq_left rfl]
          exact Ne.symm hxy
        have hr₀_y : r₀ = y := by
          rcases hr₀ with hrx | hry
          · rw [hrx] at hr₀_parent
            exact absurd hr₀_parent hx_not_root
          · exact hry
        rw [hr₀_y] at hroot
        have hxr : x.1 ≠ r := fun heq => by
          rw [← heq] at hp'
          exact hx_not_root hp'
        have hp : uf.parent r = r := by
          have hp₁ := hp'
          rw [hparent r, ite_eq_right hxr] at hp₁
          exact hp₁
        have hrank : ∀ i, (uf.link x y hy).rank i = uf.rank i := by
          intro i
          rw [rank_link]
          split
          · next hcond =>
            obtain ⟨_, heq_rk, hyr'⟩ := hcond
            exact absurd heq_rk (Nat.ne_of_lt hlt_y)
          · rfl
        have heq_class : equivClass (uf.link x y hy) r = if r = y.1 then equivClass uf x.1 ∪ equivClass uf y.1 else equivClass uf r := by
          ext i
          by_cases hyr : r = y.1
          · rw [ite_eq_left hyr, mem_equivClass, hsize, Finset.mem_union, mem_equivClass, mem_equivClass, hroot i]
            by_cases h_root : uf.rootD i = x.1 ∨ uf.rootD i = y.1
            · rw [ite_eq_left h_root]
              constructor
              · rintro ⟨hi, -⟩
                rcases h_root with h1 | h2
                · exact Or.inl ⟨hi, h1⟩
                · exact Or.inr ⟨hi, h2⟩
              · rintro (⟨hi, _⟩ | ⟨hi, _⟩)
                · exact ⟨hi, hyr.symm⟩
                · exact ⟨hi, hyr.symm⟩
            · rw [ite_eq_right h_root]
              constructor
              · rintro ⟨hi, heq⟩
                exact Or.inr ⟨hi, heq.trans hyr⟩
              · rintro (⟨hi, h1⟩ | ⟨hi, h2⟩)
                · exact absurd (Or.inl h1) h_root
                · exact absurd (Or.inr h2) h_root
          · rw [ite_eq_right hyr, mem_equivClass, hsize, mem_equivClass, hroot i]
            by_cases h_root : uf.rootD i = x.1 ∨ uf.rootD i = y.1
            · rw [ite_eq_left h_root]
              constructor
              · rintro ⟨hi, heq⟩
                exact absurd heq.symm hyr
              · rintro ⟨hi, heq⟩
                rcases h_root with h1 | h2
                · exact absurd (h1.symm.trans heq) hxr
                · exact absurd (heq.symm.trans h2) hyr
            · rw [ite_eq_right h_root]
        by_cases hyr : r = y.1
        · subst hyr
          rw [heq_class, ite_eq_left rfl]
          have h_filter_eq : ((equivClass uf x.1 ∪ equivClass uf y.1).filter (fun z => a ≤ (uf.link x y hy).rank z)) =
                             ((equivClass uf x.1).filter (fun z => a ≤ uf.rank z)) ∪
                             ((equivClass uf y.1).filter (fun z => a ≤ uf.rank z)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_union]
            rw [hrank i]
            constructor
            · rintro ⟨h1 | h2, h3⟩
              · exact Or.inl ⟨h1, h3⟩
              · exact Or.inr ⟨h2, h3⟩
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
              · exact ⟨Or.inl h1, h2⟩
              · exact ⟨Or.inr h1, h2⟩
          rw [h_filter_eq]
          have h_disj : Disjoint (equivClass uf x.1) (equivClass uf y.1) := disjoint_equivClass_of_ne uf hxy
          have h_disj_filter : Disjoint ((equivClass uf x.1).filter (fun z => a ≤ uf.rank z)) ((equivClass uf y.1).filter (fun z => a ≤ uf.rank z)) :=
            Finset.disjoint_filter_filter h_disj
          rw [Finset.card_union_of_disjoint h_disj_filter, Finset.card_union_of_disjoint h_disj, Nat.mul_add, Nat.mul_add]
          have hp_x : uf.parent x.1 = x.1 := hx
          have h1 := h (a := a) x.2 hp_x
          have h2 := h (a := a) hr hy
          exact Nat.add_le_add h1 h2
        · rw [heq_class, ite_eq_right hyr]
          have h_filter_eq : ((equivClass uf r).filter (fun z => a ≤ (uf.link x y hy).rank z)) =
                             ((equivClass uf r).filter (fun z => a ≤ uf.rank z)) := by
            ext i
            simp only [Finset.mem_filter]
            rw [hrank i]
          rw [h_filter_eq]
          exact h hr hp
      · have heq_rk : uf.rank x.1 = uf.rank y.1 := le_antisymm (Nat.le_of_not_lt hlt) (Nat.le_of_not_lt hlt_y)
        have hparent : ∀ i, (uf.link x y hy).parent i = if x.1 = i then y.1 else uf.parent i := by
          intro i
          rw [Batteries.UnionFind.parent_link hy]
          have hxy_false : (x.1 = y.1) = False := eq_false hxy
          have hlt_false : (uf.rank y.1 < uf.rank x.1) = False := eq_false hlt
          simp only [hxy_false, hlt_false, ite_false]
        have hx_not_root : (uf.link x y hy).parent x.1 ≠ x.1 := by
          rw [hparent x.1, ite_eq_left rfl]
          exact Ne.symm hxy
        have hr₀_y : r₀ = y := by
          rcases hr₀ with hrx | hry
          · rw [hrx] at hr₀_parent
            exact absurd hr₀_parent hx_not_root
          · exact hry
        rw [hr₀_y] at hroot
        have hxr : x.1 ≠ r := fun heq => by
          rw [← heq] at hp'
          exact hx_not_root hp'
        have hp : uf.parent r = r := by
          have hp₁ := hp'
          rw [hparent r, ite_eq_right hxr] at hp₁
          exact hp₁
        have hrank : ∀ i, (uf.link x y hy).rank i = if y.1 = i then uf.rank y.1 + 1 else uf.rank i := by
          intro i
          rw [rank_link]
          simp [hxy, heq_rk]
        have heq_class : equivClass (uf.link x y hy) r = if r = y.1 then equivClass uf x.1 ∪ equivClass uf y.1 else equivClass uf r := by
          ext i
          by_cases hyr : r = y.1
          · rw [ite_eq_left hyr, mem_equivClass, hsize, Finset.mem_union, mem_equivClass, mem_equivClass, hroot i]
            by_cases h_root : uf.rootD i = x.1 ∨ uf.rootD i = y.1
            · rw [ite_eq_left h_root]
              constructor
              · rintro ⟨hi, -⟩
                rcases h_root with h1 | h2
                · exact Or.inl ⟨hi, h1⟩
                · exact Or.inr ⟨hi, h2⟩
              · rintro (⟨hi, _⟩ | ⟨hi, _⟩)
                · exact ⟨hi, hyr.symm⟩
                · exact ⟨hi, hyr.symm⟩
            · rw [ite_eq_right h_root]
              constructor
              · rintro ⟨hi, heq⟩
                exact Or.inr ⟨hi, heq.trans hyr⟩
              · rintro (⟨hi, h1⟩ | ⟨hi, h2⟩)
                · exact absurd (Or.inl h1) h_root
                · exact absurd (Or.inr h2) h_root
          · rw [ite_eq_right hyr, mem_equivClass, hsize, mem_equivClass, hroot i]
            by_cases h_root : uf.rootD i = x.1 ∨ uf.rootD i = y.1
            · rw [ite_eq_left h_root]
              constructor
              · rintro ⟨hi, heq⟩
                exact absurd heq.symm hyr
              · rintro ⟨hi, heq⟩
                rcases h_root with h1 | h2
                · exact absurd (h1.symm.trans heq) hxr
                · exact absurd (heq.symm.trans h2) hyr
            · rw [ite_eq_right h_root]
        by_cases hyr : r = y.1
        · subst hyr
          rw [heq_class, ite_eq_left rfl]
          by_cases ha : a ≤ uf.rank y.1
          · have h_filter_eq : ((equivClass uf x.1 ∪ equivClass uf y.1).filter (fun z => a ≤ (uf.link x y hy).rank z)) =
                               ((equivClass uf x.1).filter (fun z => a ≤ uf.rank z)) ∪
                               ((equivClass uf y.1).filter (fun z => a ≤ uf.rank z)) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_union]
              rw [hrank i]
              by_cases hyi : y.1 = i
              · subst hyi
                have h_ay1 : a ≤ uf.rank y.1 + 1 := Nat.le_trans ha (Nat.le_add_right _ _)
                have hy_mem : y.1 ∈ equivClass uf y.1 := mem_equivClass.mpr ⟨y.2, Batteries.UnionFind.rootD_eq_self.mpr hy⟩
                constructor
                · intro _
                  exact Or.inr ⟨hy_mem, ha⟩
                · intro h_mem
                  rcases h_mem with hx_mem | hy_mem_eq
                  · exact False.elim (Finset.disjoint_left.mp (disjoint_equivClass_of_ne uf hxy) hx_mem.1 hy_mem)
                  · exact ⟨Or.inr hy_mem_eq.1, by simpa using h_ay1⟩
              · rw [ite_eq_right hyi]
                constructor
                · rintro ⟨h1 | h2, h3⟩
                  · exact Or.inl ⟨h1, h3⟩
                  · exact Or.inr ⟨h2, h3⟩
                · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                  · exact ⟨Or.inl h1, h2⟩
                  · exact ⟨Or.inr h1, h2⟩
            rw [h_filter_eq]
            have h_disj : Disjoint (equivClass uf x.1) (equivClass uf y.1) := disjoint_equivClass_of_ne uf hxy
            have h_disj_filter : Disjoint ((equivClass uf x.1).filter (fun z => a ≤ uf.rank z)) ((equivClass uf y.1).filter (fun z => a ≤ uf.rank z)) :=
              Finset.disjoint_filter_filter h_disj
            rw [Finset.card_union_of_disjoint h_disj_filter, Finset.card_union_of_disjoint h_disj, Nat.mul_add, Nat.mul_add]
            have hp_x : uf.parent x.1 = x.1 := hx
            have h1 := h (a := a) x.2 hp_x
            have h2 := h (a := a) hr hy
            exact Nat.add_le_add h1 h2
          · by_cases hay : a = uf.rank y.1 + 1
            · have h_eq : ((equivClass uf x.1 ∪ equivClass uf y.1).filter (fun z => a ≤ (uf.link x y hy).rank z)) ⊆ {y.1} := by
                intro i hi
                rw [Finset.mem_filter, Finset.mem_union, hrank i] at hi
                by_cases hyi : y.1 = i
                · subst hyi
                  exact Finset.mem_singleton.mpr rfl
                · rw [ite_eq_right hyi] at hi
                  have hrki : uf.rank i ≤ uf.rank y.1 := by
                    rcases hi.1 with hx_class | hy_class
                    · have h_le_x := Batteries.UnionFind.le_rank_root (self := uf) (x := i)
                      have h_root_x : uf.rootD i = x.1 := (mem_equivClass.mp hx_class).2
                      rw [h_root_x, heq_rk] at h_le_x
                      exact h_le_x
                    · have h_le_y := Batteries.UnionFind.le_rank_root (self := uf) (x := i)
                      have h_root_y : uf.rootD i = y.1 := (mem_equivClass.mp hy_class).2
                      rw [h_root_y] at h_le_y
                      exact h_le_y
                  have h_lt : uf.rank i < a := by
                    rw [hay]
                    exact Nat.lt_succ_of_le hrki
                  exact absurd hi.2 (Nat.not_le_of_lt h_lt)
              have h_filter_le : ((equivClass uf x.1 ∪ equivClass uf y.1).filter (fun z => a ≤ (uf.link x y hy).rank z)).card ≤ 1 :=
                (Finset.card_le_card h_eq).trans (Finset.card_singleton y.1).le
              have h_lhs : 2 ^ a * ((equivClass uf x.1 ∪ equivClass uf y.1).filter (fun z => a ≤ (uf.link x y hy).rank z)).card ≤ 2 ^ a :=
                (Nat.mul_le_mul_left (2 ^ a) h_filter_le).trans_eq (Nat.mul_one (2 ^ a))
              have h_a_le : 2 ^ a = 2 * 2 ^ (uf.rank y.1) := by
                rw [hay, Nat.pow_succ, Nat.mul_comm]
              have h_size : 2 ^ (uf.rank y.1) ≤ (equivClass uf y.1).card := h_valid y.2 hy
              have h_rhs : 2 * 2 ^ (uf.rank y.1) ≤ 2 * (equivClass uf x.1 ∪ equivClass uf y.1).card := by
                have h_le : 2 ^ (uf.rank y.1) ≤ (equivClass uf x.1 ∪ equivClass uf y.1).card := by
                  have h_sub : (equivClass uf y.1) ⊆ (equivClass uf x.1 ∪ equivClass uf y.1) := Finset.subset_union_right
                  exact h_size.trans (Finset.card_le_card h_sub)
                exact Nat.mul_le_mul_left 2 h_le
              exact (h_lhs.trans_eq h_a_le).trans h_rhs
            · have h_eq : ((equivClass uf x.1 ∪ equivClass uf y.1).filter (fun z => a ≤ (uf.link x y hy).rank z)) = ∅ := by
                ext i
                simp only [Finset.mem_filter, Finset.mem_union]
                constructor
                · rintro ⟨h_mem, h_mem2⟩
                  rw [hrank i] at h_mem2
                  by_cases hyi : y.1 = i
                  · rw [ite_eq_left hyi] at h_mem2
                    have h_ne : uf.rank y.1 + 1 ≠ a := fun h => hay h.symm
                    have h_gt : uf.rank y.1 + 1 < a := Nat.lt_of_le_of_ne (Nat.lt_of_not_le ha) h_ne
                    exact absurd h_mem2 (Nat.not_le_of_lt h_gt)
                  · rw [ite_eq_right hyi] at h_mem2
                    have hrki : uf.rank i ≤ uf.rank y.1 := by
                      rcases h_mem with hx_class | hy_class
                      · have h_le_x := Batteries.UnionFind.le_rank_root (self := uf) (x := i)
                        have h_root_x : uf.rootD i = x.1 := (mem_equivClass.mp hx_class).2
                        rw [h_root_x, heq_rk] at h_le_x
                        exact h_le_x
                      · have h_le_y := Batteries.UnionFind.le_rank_root (self := uf) (x := i)
                        have h_root_y : uf.rootD i = y.1 := (mem_equivClass.mp hy_class).2
                        rw [h_root_y] at h_le_y
                        exact h_le_y
                    have h_lt : uf.rank i < a := Nat.lt_of_le_of_lt hrki (Nat.lt_of_not_le ha)
                    exact absurd h_mem2 (Nat.not_le_of_lt h_lt)
                · rintro ⟨⟩
              rw [h_eq]
              exact Nat.zero_le _
        · rw [heq_class, ite_eq_right hyr]
          have h_filter_eq : ((equivClass uf r).filter (fun z => a ≤ (uf.link x y hy).rank z)) =
                             ((equivClass uf r).filter (fun z => a ≤ uf.rank z)) := by
            ext i
            simp only [Finset.mem_filter]
            rw [hrank i]
            by_cases hyi : y.1 = i
            · subst hyi
              constructor
              · rintro ⟨hi, _⟩
                have h_root_i : uf.rootD y.1 = r := (mem_equivClass.mp hi).2
                have h_root_y : uf.rootD y.1 = y.1 := Batteries.UnionFind.rootD_eq_self.mpr hy
                rw [h_root_y] at h_root_i
                exact absurd h_root_i.symm hyr
              · rintro ⟨hi, _⟩
                have h_root_i : uf.rootD y.1 = r := (mem_equivClass.mp hi).2
                have h_root_y : uf.rootD y.1 = y.1 := Batteries.UnionFind.rootD_eq_self.mpr hy
                rw [h_root_y] at h_root_i
                exact absurd h_root_i.symm hyr
            · rw [ite_eq_right hyi]
          rw [h_filter_eq]
          exact h hr hp
end RankCount
@[expose] def block (rank : ℕ) : ℕ := Nat.logStar rank

@[expose] def nodeCredit (uf : Batteries.UnionFind) (x : Fin uf.size) : ℕ :=
  if uf.parent x.1 = x.1 then 0 else
    let b := block (uf.rank (uf.parent x.1))
    if block (uf.rank x.1) = b then
      Nat.twoTower b - uf.rank (uf.parent x.1)
    else 0

@[expose] def nodeCreditSum (uf : Batteries.UnionFind) : ℕ :=
  ((List.finRange uf.size).map (fun x => nodeCredit uf x)).sum

@[expose] def nonRootInBlock (uf : Batteries.UnionFind) (b : ℕ) : Finset (Fin uf.size) :=
  Finset.filter (fun x => uf.parent x.1 ≠ x.1 ∧ block (uf.rank x.1) = b) Finset.univ

@[expose] def blockBudget (uf : Batteries.UnionFind) : ℕ → ℕ
  | 0 => 2 * uf.size - 2 * (nonRootInBlock uf 0).card
  | b + 1 => 2 * uf.size - Nat.twoTower (b + 1) * (nonRootInBlock uf (b + 1)).card

@[expose] def potential (uf : Batteries.UnionFind) : ℕ :=
  nodeCreditSum uf + ((List.range (Nat.logStar uf.size + 2)).map (fun b => blockBudget uf b)).sum

theorem amortizedBound (n : ℕ) :
    Cslib.DataStructure.Amortized (impl n) id (fun _ c => potential c.uf) (fun _ _ => 2 * Nat.logStar n + 3) := by
  sorry

end Cslib.DataStructure.DisjointSet.UnionFind
