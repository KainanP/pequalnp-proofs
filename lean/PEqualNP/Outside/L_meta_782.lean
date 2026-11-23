import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
-- The joint support count follows the project's circuit support lemma.
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _


def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L


def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega


abbrev Input (n : ℕ) := Fin n → Bool
def basic (p : Fin n) : Input n := fun q => decide (q=p)
def ones (f : Input n → Bool) := Finset.univ.filter (fun p => f (basic p)=true)
def Dom (f : Input n → Bool) := ∀ p x, x p = true → f (basic p) = true → f x = true
def Good (S T : Finset (Fin n)) (f : Input n → Bool) :=
  ∀ p x, f (basic p) = true → p ∉ T → (∀ a ∈ T, a ∉ S → x a=true) → f x=true

theorem cnt_free {L : List (Finset (Fin n))} {t} (h : Cnt t L) {T : Finset (Fin n)}
    (hc : T.card ≤ 1) : Cnt t (L ++ [T]) := by
  intro W
  let U := W.erase L.length
  by_cases hm : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [T]).getD j ∅) ⊆ (U.biUnion fun j => L.getD j ∅) ∪ T := by
      intro a ha
      obtain ⟨j,hj,h⟩ := Finset.mem_biUnion.mp ha
      by_cases eq : j=L.length
      · subst j; exact Finset.mem_union_right _ ((getD_snoc_eq L T ∅) ▸ h)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨j,Finset.mem_erase.mpr ⟨eq,hj⟩,(getD_snoc_ne L T ∅ j eq) ▸ h⟩)
    have h₁ := Finset.card_le_card hsub
    have h₂ := Finset.card_union_le (U.biUnion fun j => L.getD j ∅) T
    have h₃ := h U
    have h₄ : U.card + 1 = W.card := Finset.card_erase_add_one hm
    omega
  · have eq : (W.biUnion fun j => (L ++ [T]).getD j ∅) = (W.biUnion fun j => L.getD j ∅) :=
      Finset.biUnion_congr rfl fun j hj => getD_snoc_ne _ _ _ _ (fun e => hm (e ▸ hj))
    rw [eq]; exact h W

theorem stepImp (g : Gate) (hop : g.op=.and ∨ g.op=.or) (a b : ℕ → Bool)
    (h : ∀ j ∈ g.inputs, a j=true → b j=true) :
    g.op.eval (g.inputs.map a)=true → g.op.eval (g.inputs.map b)=true := by
  obtain h1 | h1 := hop
  · rw [h1]; simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    exact fun h2 i hi => h i hi (h2 i hi)
  · rw [h1]; simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hs⟩
    exact ⟨i,hi,h i hi hs⟩

def V (gs : List Gate) (j : ℕ) (x : Input n) :=
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD j false

def gateFun (gs : List Gate) (g : Gate) (x : Input n) :=
  g.op.eval (g.inputs.map fun j => V gs j x)

theorem V_snoc (gs : List Gate) (g : Gate) (j : ℕ) (x : Input n) :
    V (gs++[g]) j x = if j=n+gs.length then gateFun gs g x else V gs j x := by
  have sz (t : List Gate) (l : List Bool) : ((Circuit.mk t 0).wires l).length = l.length+t.length := by
    induction t generalizing l with
    | nil => simp [Circuit.wires]
    | cons v t ih =>
      change ((Circuit.mk t 0).wires (l++[_])).length = _
      rw [ih]; simp; omega
  let w := (Circuit.mk gs 0).wires (List.ofFn x)
  have hw : w.length=n+gs.length := by simp [w,sz]
  change ((gs++[g]).foldl _ (List.ofFn x)).getD j false = _
  rw [List.foldl_append]
  change (w++[gateFun gs g x]).getD j false = _
  split
  · rename_i h; rw [h,← hw,getD_snoc_eq]
  · rename_i h; exact getD_snoc_ne _ _ _ _ (fun e => h (e.trans hw))

theorem allDom (gs : List Gate) (hm : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (j : ℕ) : Dom (@V n gs j) := by
  induction gs using List.reverseRecOn generalizing j with
  | nil =>
    intro p x hp h
    by_cases hj : j<n
    · have he : (⟨j,hj⟩ : Fin n) = p := by simpa [V,Circuit.wires,basic,List.getD,hj] using h
      simpa [V,Circuit.wires,List.getD,hj,he] using hp
    · simp [V,Circuit.wires,List.getD,hj] at h
  | append_singleton gs g ih =>
    intro p x hp h
    simp only [V_snoc] at h ⊢
    by_cases eq : j=n+gs.length
    · simp only [if_pos eq] at h ⊢
      apply stepImp _ (hm g (by simp)) _ _ _ h
      intro a _ hv
      exact ih (fun u hu => hm u (List.mem_append_left _ hu)) a p x hp hv
    · simp only [if_neg eq] at h ⊢
      exact ih (fun u hu => hm u (List.mem_append_left _ hu)) j p x hp h

theorem free_rep (S : Finset (Fin n)) (f : Input n → Bool) (hd : Dom f)
    (hn : ¬(ones f ⊆ S ∧ 2 ≤ (ones f).card)) :
    ∃ T : Finset (Fin n), T.card ≤ 1 ∧ Good S T f := by
  classical
  by_cases hs : ones f ⊆ S
  · refine ⟨ones f, by by_contra! h; exact hn ⟨hs,by omega⟩,?_⟩
    intro p x h hp _
    exact (hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)).elim
  · obtain ⟨a,ha,hout⟩ := Finset.not_subset.mp hs
    refine ⟨{a},by simp,?_⟩
    intro p x _ _ hx
    exact hd a x (hx a (by simp) hout) (Finset.mem_filter.mp ha).2

theorem supports {m} (S : Fin m → Finset (Fin n))
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (gs : List Gate)
    (hf : ∀ g ∈ gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length = 2) :
    ∃ (b : Fin m → ℕ) (M : Fin m → List (Finset (Fin n))),
      (∑ i, b i) ≤ gs.length ∧ ∀ i, (M i).length = n+gs.length ∧ Cnt (b i) (M i) ∧
      ∀ j, Good (S i) ((M i).getD j ∅) (V gs j) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ => 0, fun _ => inputSupps n, by simp, ?_⟩
    intro i
    refine ⟨by simp [inputSupps],cnt_inputs,?_⟩
    intro j p x hv hp hx
    by_cases hj : j<n
    · have he : (⟨j,hj⟩ : Fin n)=p := by simpa [V,Circuit.wires,List.getD,hj,basic] using hv
      exact (hp (by simp [inputSupps,List.getD,hj,he])).elim
    · simp [V,Circuit.wires,List.getD,hj] at hv
  | append_singleton gs g ih =>
    have hOld : ∀ u ∈ gs, (u.op=.and ∨ u.op=.or) ∧ u.inputs.length=2 :=
      fun u hu => hf u (List.mem_append_left _ hu)
    have hG := hf g (by simp)
    obtain ⟨b,M,hsum,hold⟩ := ih hOld
    let f := @gateFun n gs g
    let priv (i : Fin m) := ones f ⊆ S i ∧ 2 ≤ (ones f).card
    let coin (i : Fin m) := if priv i then 1 else 0
    have unique (i j) (hi : priv i) (hj : priv j) : i=j := by
      by_contra hn
      have sub : ones f ⊆ S i ∩ S j := fun a ha => Finset.mem_inter.mpr ⟨hi.1 ha,hj.1 ha⟩
      have t := (Finset.card_le_card sub).trans (hpair i j hn)
      have := hi.2
      omega
    have cost : (∑ i, coin i) ≤ 1 := by
      by_cases h : ∃ i, priv i
      · obtain ⟨i,hi⟩ := h
        rw [Finset.sum_eq_single i]
        · simp [coin,hi]
        · intro j _ hj
          have hnot : ¬ priv j := fun h => hj (unique j i h hi)
          exact if_neg hnot
        · simp
      · simp [coin,show ∀ i, ¬priv i from fun i hi => h ⟨i,hi⟩]
    have hfdom : Dom f := by
      intro p x hx h
      apply stepImp g hG.1 _ _ _ h
      intro j _ hv
      exact allDom gs (fun a ha => (hOld a ha).1) j p x hx hv
    have add (i : Fin m) : ∃ T, Cnt (b i + coin i) (M i ++ [T]) ∧ Good (S i) T f := by
      by_cases hc : priv i
      · refine ⟨gateSupp (M i) g,by simpa [coin,hc] using cnt_step (b i) (M i) g hG.2.le (hold i).2.1,?_⟩
        intro p x h hp hx
        apply stepImp g hG.1 _ _ _ h
        intro j hj hv
        have ins (a) (ha : a ∈ (M i).getD j ∅) : a ∈ gateSupp (M i) g :=
          (mem_gateSupp _ _ _).mpr ⟨j,hj,ha⟩
        exact (hold i).2.2 j p x hv (fun h => hp (ins p h)) (fun a h => hx a (ins a h))
      · obtain ⟨T,hT,hgood⟩ := free_rep (S i) f hfdom hc
        exact ⟨T,by simpa [coin,hc] using cnt_free (hold i).2.1 hT,hgood⟩
    choose t h using add
    refine ⟨fun i => b i+coin i,fun i => M i++[t i],?_,?_⟩
    · rw [Finset.sum_add_distrib]; simp only [List.length_append,List.length_singleton]; omega
    · intro i
      refine ⟨by simp [(hold i).1,Nat.add_assoc],(h i).1,?_⟩
      intro j
      by_cases eq : j = n+gs.length
      · have hlen : j = (M i).length := eq.trans (hold i).1.symm
        have hval : @V n (gs++[g]) j = f := by funext x; simp [V_snoc,eq,f]
        rw [hval,show (M i++[t i]).getD j ∅ = t i from hlen ▸ getD_snoc_eq _ _ _]
        exact (h i).2
      · have hval : @V n (gs++[g]) j = V gs j := by funext x; simp [V_snoc,eq]
        rw [hval,getD_snoc_ne _ _ _ _ (fun e => eq (e.trans (hold i).1))]
        exact (hold i).2.2 j

end PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_782 in
theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hpair _ hfan _ hoff hck hsize
  obtain ⟨b,M,hb,hgood⟩ := supports S hpair C.gates hfan
  apply le_trans (Finset.sum_le_sum (g := b) ?_) hb
  intro i _
  let T := (M i).getD (o i) ∅
  have hT : T.card ≤ b i + 1 := by
    have h := (hgood i).2.1 {o i}
    simpa [T] using h
  by_contra! hlt
  have hA : c i + 1 ≤ (ones (@V n C.gates (o i))).card := hsize i
  have hns : ¬ones (@V n C.gates (o i)) ⊆ T := by
    intro sub
    have := Finset.card_le_card sub
    omega
  obtain ⟨p,ha,hp⟩ := Finset.not_subset.mp hns
  let X := T \ S i
  let x : Input n := fun q => decide (q ∈ X)
  have hwt : (Finset.univ.filter (fun q : Fin n => x q=true)).card ≤ k := by
    have he : Finset.univ.filter (fun q : Fin n => x q=true) = X := by ext q; simp [x]
    rw [he]
    have hc := Finset.card_le_card (Finset.sdiff_subset (s:=T) (t:=S i))
    change (T \ S i).card ≤ k
    have := hck i
    omega
  have ho := hoff i x hwt (by intro q hq; simp [x,X,hq])
  have ht := (hgood i).2.2 (o i) p x (Finset.mem_filter.mp ha).2 hp
    (by intro a hmem hn; exact decide_eq_true (Finset.mem_sdiff.mpr ⟨hmem,hn⟩))
  change V C.gates (o i) x = false at ho
  rw [ho] at ht
  contradiction
