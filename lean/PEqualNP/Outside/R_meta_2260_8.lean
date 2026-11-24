import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 1300000 in
theorem PEqualNP.Outside.R_meta_2260_8
  (table : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7), (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)]; let row := fun (t : Fin 40) (i : Fin 11) => (([513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768, 15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546] : List Nat).getD t.val 0).testBit i.val;
  (∀ t : Fin 40, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (row t) = decide (t.val<16)) ∧ ∀ x : Fin 11 → Bool, Maximal (fun z => PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ z=false) x → ∃ t : Fin 40, 16≤t.val ∧ row t=x)
  (critical : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j a b : Nat), IsLeastAO G C → j<C.size → (gateAt C j).op=.and → (gateAt C j).inputs=[a,b] → ∀ p q : Bool, (p≠q ∨ p=true ∧ q=true ∧ IsDirtyAnd n G C j) → ∃ x : Fin n → Bool, Maximal (fun y => graphFun G ∅ y=false) x ∧ (C.wires (List.ofFn x)).getD a false=p ∧ (C.wires (List.ofFn x)).getD b false=q)
  (search : let row := fun (t : Fin 40) (i : Fin 11) => (([513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768, 15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546] : List Nat).getD t.val 0).testBit i.val; ¬∃ (C : Circuit) (g h : Nat), IsAO2 11 C ∧ C.size≤21 ∧ InCone 11 C g h ∧
    (∀ t : Fin 40, C.eval (List.ofFn (row t)) = decide (t.val<16)) ∧
    ∀ j<C.size, ∀ a b : Nat, (gateAt C j).op=.and → (gateAt C j).inputs=[a,b] →
      let w := fun (v : Nat) (t : Fin 40) => (C.wires (List.ofFn (row t))).getD v false;
      (∀ t : Fin 40, 16≤t.val → w (11+j) t=true → j=g ∨ j=h) ∧
      ∀ p q : Bool, (p≠q ∨ p=true ∧ q=true ∧ (j=g ∨ j=h)) → ∃ t : Fin 40, 16≤t.val ∧ w a t=p ∧ w b t=q) :
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x12 ∈ x9,             have x14 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x12;             (∀ x15 ∈ x14 (0 : Fin (2 : ℕ)), ∀ x17 ∈ x14 (1 : Fin (2 : ℕ)), x1.Adj x15 x17) ∧ ((x14 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x14 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x13 x14 : Fin (11 : ℕ)), s(x13, x14) ∈ x11 → ∃ x16 ∈ x9, ∃ (x17 : Fin (2 : ℕ)) (x18 : ℕ), (x18 = x4 ∨ x18 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x16 x17) x18 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x18 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x15 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x15 → x15.card ≤ (x9 \ x10).card) → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 → (22 : ℕ) ≤ x3.size := by
  let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7), (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)]
  let std : DecidableRel G.Adj := inferInstanceAs (DecidableRel (PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7), (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)]).Adj)
  classical
  intro H inst C g h eqG least form
  dsimp only
  intro _ _ _ _ junkEq nested
  subst H
  have ei : inst=std := Subsingleton.elim _ _
  subst inst
  let row := fun (t : Fin 40) (i : Fin 11) => (([513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768, 15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546] : List Nat).getD t.val 0).testBit i.val
  have labels := table.1
  have allMax := table.2
  by_contra! short
  apply search
  refine ⟨C,g,h,least.1,by omega,nested,?_,?_⟩
  · intro t
    exact (congrFun least.2.1 (row t)).trans (labels t)
  · intro j hj a b op ins
    have marked : j=g ∨ j=h ↔ IsDirtyAnd 11 G C j := by
      have mem : j∈junk G C ↔ IsDirtyAnd 11 G C j := by
        change j∈(Finset.range C.gates.length).filter (fun k => IsDirtyAnd 11 G C k) ↔ _
        exact ⟨fun z => (Finset.mem_filter.mp z).2,fun z => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,z⟩⟩
      rw [←mem,junkEq,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · intro t ht yes
      apply marked.mpr; refine ⟨op,hj,row t,yes,?_⟩
      have status : graphFun G ∅ (row t)=decide (t.val<16) := labels t
      exact status.trans (by simp [show ¬t.val<16 from by omega])
    · intro p q admissible
      have want : p≠q ∨ p=true ∧ q=true ∧ IsDirtyAnd 11 G C j := by
        rcases admissible with ne | ⟨hp,hq,flag⟩
        · exact Or.inl ne
        · exact Or.inr ⟨hp,hq,marked.mp flag⟩
      obtain ⟨x,hx,va,vb⟩ := critical 11 G C j a b least hj op ins p q want
      obtain ⟨t,ok,et⟩ := allMax x hx
      change row t=x at et
      subst x
      exact ⟨t,ok,va,vb⟩
