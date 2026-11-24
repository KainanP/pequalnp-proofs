import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection

set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.R_meta_1782_8 (frontier : ∀ (N : Nat) (C : Circuit) (x : Fin (N+N) → Bool), Monotone2 C → circuitFun (N+N) C x=true → (∀ l : Fin N, x (Fin.natAdd N l)=true → circuitFun (N+N) C (Function.update x (Fin.natAdd N l) false)=false) → ∀ t : Nat, 0<t → let F := fun i : Nat => Finset.univ.filter fun l : Fin N => (C.wires (List.ofFn x)).getD i false=true ∧ (C.wires (List.ofFn (Function.update x (Fin.natAdd N l) false))).getD i false=false; Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ t*(1+Nat.card {j : Fin C.size // t<(F (N+N+j.val)).card ∧ (gateAt C j.val).op=.and ∧ ¬F (opnd C j.val 0)⊆F (opnd C j.val 1) ∧ ¬F (opnd C j.val 1)⊆F (opnd C j.val 0)}))
  (residual : ∀ (q N : Nat) (B : Fin N → Finset (Fin N)) (C : Circuit), 199≤q → N=q^2+q+1 → (∀ l, (B l).card=q+1) → (∀ p r, p≠r → ∃! l, p∈B l ∧ r∈B l) → Monotone2 C → RightOnIncidentPairs B C →
    let miss := fun z : Fin (N+N) → Bool => ¬∃ p l, p∈B l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true;
    (∀ z, Fintype.card {l : Fin N // z (Fin.natAdd N l)=true}≤q → miss z → circuitFun (N+N) C z=false) → ∀ x, miss x → circuitFun (N+N) C x=true → let F := fun i : Nat => Finset.univ.filter fun l : Fin N => (C.wires (List.ofFn x)).getD i false=true ∧ (C.wires (List.ofFn (Function.update x (Fin.natAdd N l) false))).getD i false=false; (∀ t : Nat, 0<t → q<t*(1+Nat.card {j : Fin C.size // t<(F (N+N+j.val)).card ∧ (gateAt C j.val).op=.and ∧ ¬F (opnd C j.val 0)⊆F (opnd C j.val 1) ∧ ¬F (opnd C j.val 1)⊆F (opnd C j.val 0)})) → N*q ≤ 100*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → ∀ (x13 : Fin (x2 + x2) → Bool), (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.true → x1 < Fintype.card { x16 : Fin x2 // x13 (Fin.natAdd x2 x16) = Bool.true } → (∀ (x17 : Fin x2), x13 (Fin.natAdd x2 x17) = Bool.true → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (Function.update x13 (Fin.natAdd x2 x17) Bool.false) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hN lines unique mono accepts sound x no yes above minimal
  let B (l : Fin N) := Finset.univ.filter (fun p => I p l)
  have mem (p l : Fin N) : p∈B l ↔ I p l := by simp [B]
  have cardB (l : Fin N) : (B l).card=q+1 := by simpa [Fintype.card_subtype,B] using lines l
  have common (p r : Fin N) (ne : p≠r) : ∃! l, p∈B l ∧ r∈B l := by simpa only [mem] using unique p r ne
  have right : RightOnIncidentPairs B C := by
    intro l p hp
    let pair (k : Fin (N+N)) := decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N l)
    have eq : List.ofFn pair = incidenceInput {p} {l} := by
      rw [List.ofFn_add]
      unfold incidenceInput
      congr 1
      · apply congrArg List.ofFn; funext i;apply Bool.eq_iff_iff.mpr
        simp only [pair,decide_eq_true_eq,Finset.mem_singleton,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd,Fin.val_castLE,Fin.val_addNat];omega
      · apply congrArg List.ofFn; funext i;apply Bool.eq_iff_iff.mpr
        simp only [pair,decide_eq_true_eq,Finset.mem_singleton,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd,Fin.val_castLE,Fin.val_addNat];omega
    rw [←eq]; exact accepts p l ((mem p l).mp hp)
  apply residual q N B C hq hN cardB common mono right
  · intro z hl neg;apply sound z hl;simpa only [←mem] using neg
  · simpa only [mem] using no
  · exact yes
  · intro t ht;exact above.trans_le (frontier N C x mono yes minimal t ht)
