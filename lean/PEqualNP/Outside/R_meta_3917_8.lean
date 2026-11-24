import PEqualNP.Defs
open PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3917_8
  (transport : ∀ (n : Nat) (C : BinaryCircuit) (p : Equiv.Perm (Fin n)),
    let model := fun B : BinaryCircuit => (∀ g∈B.gates, ∃ p q : Bool, g.op=fun a b => (a==p) && (b==q)) ∧ (∀ j : Fin B.size, (B.gates.get j).left<(B.gates.get j).right ∧ (B.gates.get j).right<n+j.val);
    model C → ∃ D : BinaryCircuit, D.size=C.size ∧ model D ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x)=C.eval (List.ofFn (fun i => x (p i))))
  (remaining : ∀ (a : Fin 9), a.val∈([0,2,3,4,7] : List Nat) → ∀ (p q phase : Bool) (B : BinaryCircuit),
     (∀ g∈B.gates, ∃ p q : Bool, g.op=fun a b => (a==p) && (b==q)) → (∀ j : Fin B.size, (B.gates.get j).left<(B.gates.get j).right ∧ (B.gates.get j).right<11+j.val) →
     (∀ x : Fin 9 → Bool, let u := x 0 || x 1; (B.eval (List.ofFn x ++ [u,(x a==p) && (u==q)]) != phase) = ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))) → 13≤B.size) :
have x1 : PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x1 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ x2 ∈ x1.gates, ∃ (x4 : Bool) (x5 : Bool), x2.op = fun (x6 x7 : Bool) => x6 == x4 && x7 == x5; have x2 : ℕ → PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x2 : ℕ) (x3 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ (x4 : Fin x3.size), (x3.gates.get x4).left < (x3.gates.get x4).right ∧ (x3.gates.get x4).right < x2 + ↑x4; have x3 : (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x4 : ℕ) => x3 (Fin.ofNat (9 : ℕ) (x4 / (10 : ℕ))) && x3 (Fin.ofNat (9 : ℕ) (x4 % (10 : ℕ))); ∀ (x4 : PEqualNP.MetaComplexity.BinaryCircuit) (x5 : Bool) (x6 : (0 : ℕ) < x4.size), x1 x4 → x2 (10 : ℕ) x4 → x4.output = (10 : ℕ) + x4.size - (1 : ℕ) → (x4.gates.get (⟨(0 : ℕ), x6⟩ : Fin x4.gates.length)).right = (9 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), (x4.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ))]) != x5) = x3 x11) → (14 : ℕ) ≤ x4.size := by
  dsimp only
  intro C phase pos sg ordered last first computes
  rcases C with ⟨gates,output⟩
  cases gates with
  | nil => exact (Nat.not_lt_zero _ pos).elim
  | cons g gs =>
    let C : BinaryCircuit := ⟨g::gs,output⟩
    let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
    let W (a : Fin 9) (p q : Bool) (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 1,(x a==p) && ((x 0 || x 1)==q)]
    let s (i : Fin 9) : Fin 9 := ([1,0,5,8,6,2,4,7,3] : List (Fin 9)).getD i.val 0
    let t (i : Fin 11) : Fin 11 := ([1,0,5,8,6,2,4,7,3,9,10] : List (Fin 11)).getD i.val 0
    have involution : ∀ i, t (t i)=i := by decide +kernel
    let perm : Equiv.Perm (Fin 11) := ⟨t,t,involution,involution⟩
    have covers : ∀ a : Fin 9, a.val∈([0,2,3,4,7] : List Nat) ∨ (s a).val∈([0,2,3,4,7] : List Nat) := by decide +kernel
    have inv : ∀ x, F (fun i => x (s i))=F x := by decide +kernel
    have readRaw (a : Fin 9) (p q : Bool) (x : Fin 9 → Bool) (i : Fin 9) :
        (W a p q x).getD i.val false=x i := by
      rw [show W a p q x=List.ofFn x++_ from rfl,List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    have lifted (a : Fin 9) (p q : Bool) (x : Fin 9→Bool) (i : Fin 11) :
        (W (s a) p q x).getD (t i).val false=(W a p q (fun j => x (s j))).getD i.val false := by
      by_cases small : i.val<9
      · let j : Fin 9 := ⟨i.val,small⟩
        have tab : ∀ j : Fin 9, (t ⟨j.val,Nat.lt_trans j.isLt (by decide : 9<11)⟩).val=(s j).val := by decide +kernel
        change (W (s a) p q x).getD (t ⟨j.val,by omega⟩).val false=(W a p q (fun k => x (s k))).getD j.val false
        rw [tab,readRaw,readRaw]
      · have ends : i=9 ∨ i=10 := by have := i.isLt;rcases (by omega : i.val=9 ∨ i.val=10) with h|h <;> [left;right] <;> apply Fin.ext <;> exact h
        rcases ends with rfl|rfl <;> simp [W,s,t,List.getD_eq_getElem?_getD,List.getElem?_append,Bool.or_comm]
    have list : C.gates=g::gs := rfl
    have right : g.right=9 := first
    have ltr : g.left<g.right := (ordered ⟨0,pos⟩).1
    rw [right] at ltr
    let a : Fin 9 := ⟨g.left,ltr⟩
    obtain ⟨p,q,op⟩ := sg g (by simp [list])
    let B : BinaryCircuit := ⟨gs,C.output⟩
    have part : B.size+1=C.size := rfl
    have bs : ∀ h∈B.gates,∃ p q : Bool,h.op=fun a b => (a==p) && (b==q) := fun h m => sg h (List.mem_cons_of_mem g m)
    have bo : ∀ j : Fin B.size,(B.gates.get j).left<(B.gates.get j).right ∧ (B.gates.get j).right<11+j.val := by
      intro j
      let k : Fin C.size := ⟨j.val+1,by have := j.isLt;omega⟩
      obtain ⟨l,r⟩ := ordered k
      change (B.gates.get j).right<10+(j.val+1) at r
      exact ⟨l,by omega⟩
    have eval (x : Fin 9 → Bool) : (B.eval (W a p q x) != phase)=F x := by
      have value : C.eval (List.ofFn x ++ [x 0 || x 1])=B.eval (W a p q x) := by
        let base := List.ofFn x++[x 0 || x 1]
        have ga : base.getD g.left false=x a := by
          change (List.ofFn x++_).getD g.left false=_
          rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using ltr),List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using ltr),List.getElem_ofFn]
        have gb : base.getD g.right false=(x 0 || x 1) := by rw [right];simp [base]
        change B.eval (base++[g.op (base.getD g.left false) (base.getD g.right false)])=B.eval (W a p q x)
        rw [ga,gb,op]
        simp only [base,W,List.append_assoc,List.cons_append,List.nil_append]
      rw [←value];exact computes x
    have sufficient : 13≤B.size := by
      rcases covers a with simple|other
      · exact remaining a simple p q phase B bs bo eval
      · obtain ⟨D,ds,⟨dsign,dorder⟩,deval⟩ := transport 11 B perm ⟨bs,bo⟩
        rw [←ds];apply remaining (s a) other p q phase D dsign dorder
        intro x
        let read (l : List Bool) := fun i : Fin 11 => l.getD i.val false
        have back (l : List Bool) (h:l.length=11) : List.ofFn (read l)=l := by
          apply List.ext_getElem
          · simp [h]
          · intro i hi hj;rw [List.getElem_ofFn];exact List.getD_eq_getElem _ _ hj
        have h1 : (W (s a) p q x).length=11 := by simp [W]
        have h2 : (W a p q (fun i => x (s i))).length=11 := by simp [W]
        have matchRows : (fun i => read (W (s a) p q x) (perm i))=read (W a p q (fun i => x (s i))) := by funext i;exact lifted _ _ _ _ i
        have exchange := deval (read (W (s a) p q x))
        rw [back _ h1,matchRows,back _ h2] at exchange
        change (D.eval (W (s a) p q x) != phase)=F x
        rw [exchange,eval,inv]
    change 14≤C.size
    omega
