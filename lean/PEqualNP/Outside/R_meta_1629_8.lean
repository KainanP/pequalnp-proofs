import Mathlib.Data.Fintype.Sigma
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1629_8
  (hlin : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin x1), ∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x4 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → x1 ≤ x2.size + (1 : ℕ))
  (hnorm : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ x5.output < x1 + x5.size ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 < x10 ∧ x10 < x1 + x6)
  (gadget : ∀ (N : Nat) (C : Circuit), IsAO2 (N+N) C → C.output<N+N+C.size → (∀ i : Fin (N+N), circuitFun (N+N) C (fun j => decide (j=i))=false) → ∃ D : Circuit, IsAO2 (N+N) D ∧ D.size=C.size+1 ∧ circuitFun (N+N) D=circuitFun (N+N) C ∧ ∀ p l : Fin N, lineSingle D (N+N) (fun i => decide (N ≤ i)) p.val (N+l.val)=false ∧ lineSingle D (N+N) (fun i => decide (i < N)) p.val (N+l.val)=false)
  (dbl : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size)
  : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 100 * C.size := by
  intro q N I inst C hq hN hcard hline hmon hacc hsound
  have hNpos : 2 ≤ N := by nlinarith
  have hcast_ne_nat : ∀ (p l : Fin N), Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hsens : ∀ k : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
      (∀ j : Fin (N + N), j ≠ k → x j = y j) ∧
      circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
    intro k
    by_cases hk : k.val < N
    · let p : Fin N := ⟨k.val, hk⟩
      have hkp : k = Fin.castAdd N p := Fin.ext rfl
      let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : p ≠ p' := by
        intro h
        have hv := congrArg Fin.val h
        by_cases hp0 : p.val = 0 <;> simp [p', hp0] at hv
      obtain ⟨l, ⟨hIpl, _⟩, _⟩ := hline p p' hne
      let x : Fin (N + N) → Bool := fun j => decide (j = Fin.natAdd N l)
      let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
      refine ⟨x, y, ?_, ?_⟩
      · intro j hj
        rw [hkp] at hj
        simp only [x, y, hj, false_or]
      · have hy : circuitFun (N + N) C y = true := hacc p l hIpl
        have hx : circuitFun (N + N) C x = false := by
          apply hsound x
          · have hsub : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) ⊆ {l} := by
              intro l' hl'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, decide_eq_true_eq] at hl'
              have hval := congrArg Fin.val hl'
              simp only [Fin.val_natAdd] at hval
              exact Finset.mem_singleton.mpr (Fin.ext (by omega))
            exact (Finset.card_le_card hsub).trans (by simp; omega)
          · rintro ⟨p0, l0, _, hp0, _⟩
            simp only [x, decide_eq_true_eq] at hp0
            exact hcast_ne_nat p0 l hp0
        rw [hx, hy]
        decide
    · let l : Fin N := ⟨k.val - N, by omega⟩
      have hkl : k = Fin.natAdd N l := Fin.ext (by simp [l]; omega)
      have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l)).card := by
        rw [hcard l]; omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      have hIpl : I p l := (Finset.mem_filter.mp hp).2
      let x : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p)
      let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
      refine ⟨x, y, ?_, ?_⟩
      · intro j hj
        rw [hkl] at hj
        simp only [x, y, hj, or_false]
      · have hy : circuitFun (N + N) C y = true := hacc p l hIpl
        have hx : circuitFun (N + N) C x = false := by
          apply hsound x
          · have hemp : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) = ∅ := by
              ext l'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false, x, decide_eq_true_eq]
              intro h
              exact hcast_ne_nat p l' h.symm
            rw [hemp]
            simp
          · rintro ⟨p0, l0, _, _, hl0⟩
            simp only [x, decide_eq_true_eq] at hl0
            exact hcast_ne_nat p l0 hl0.symm
        rw [hx, hy]
        decide
  have hNsize : N ≤ C.size := by
    have h2N := hlin (N + N) C hmon hsens
    omega
  by_cases hq100 : q ≤ 100
  · calc N * q ≤ N * 100 := Nat.mul_le_mul_left N hq100
      _ = 100 * N := Nat.mul_comm N 100
      _ ≤ 100 * C.size := Nat.mul_le_mul_left 100 hNsize
  · have hqgt : 100 < q := by omega
    have hnc : ∃ x y : Fin (N + N) → Bool, circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
      obtain ⟨x, y, _, hne⟩ := hsens ⟨0, by omega⟩
      exact ⟨x, y, hne⟩
    obtain ⟨C', hmon', hsize', hfun', hout', hgates'⟩ := hnorm (N + N) C hmon hnc
    have hacc' : ∀ p l : Fin N, I p l →
        circuitFun (N + N) C' (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
      intro p l hI
      rw [hfun']
      exact hacc p l hI
    have hcard' : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1 := by
      intro l
      rw [Fintype.card_subtype]
      exact hcard l
    have hsound' : ∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C' z = false := by
      intro z hle hno
      rw [hfun']
      rw [Fintype.card_subtype] at hle
      exact hsound z hle hno
    classical
    have shape : IsAO2 (N+N) C' := by
      refine ⟨fun g h => (hmon' g h).1,?_,?_⟩
      · intro j hj i hi
        let g := C'.gates[j]
        have atg : C'.gates[j]?=some g := List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩
        have eq : NestedCover.gateAt C' j=g := List.getD_eq_getElem _ _ hj
        obtain ⟨a,b,ins,ab,live⟩ := hgates' j g atg
        rw [eq,ins] at hi;rcases List.mem_cons.mp hi with rfl | hb
        · omega
        · exact (List.mem_singleton.mp hb) ▸ live
      · intro g hg;obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp hg
        obtain ⟨a,b,ins,_,_⟩ := hgates' j g (List.getElem?_eq_some_iff.mpr ⟨hj,e⟩)
        rw [ins];rfl
    have singletonFalse (i : Fin (N+N)) : circuitFun (N+N) C' (fun j => decide (j=i))=false := by
      apply hsound'
      · rw [Fintype.card_subtype];apply le_trans (b:=1) _ (by omega)
        apply Finset.card_le_one.mpr;intro a ha b hb
        have a' : Fin.natAdd N a=i := of_decide_eq_true (Finset.mem_filter.mp ha).2
        have b' : Fin.natAdd N b=i := of_decide_eq_true (Finset.mem_filter.mp hb).2
        apply Fin.ext;have eqv := congrArg Fin.val (a'.trans b'.symm);simp only [Fin.val_natAdd] at eqv;omega
      · rintro ⟨p,l,_,hp,hl⟩
        exact hcast_ne_nat p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
    obtain ⟨D,valid,sizeD,eqD,twice⟩ := gadget N C' shape hout' singletonFalse
    have rejectD : ∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ q →
        (¬∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) → circuitFun (N+N) D z=false := by
      rw [eqD];exact hsound'
    have bound := dbl q N I D (by omega) hN hcard' hline valid rejectD
    let E := {e : Fin N × Fin N // I e.1 e.2}
    let bad (e : Fin N × Fin N) := I e.1 e.2 ∧ circuitFun (N+N) D (fun k => decide (k=Fin.castAdd N e.1 ∨ k=Fin.natAdd N e.2))=true ∧ lineSingle D (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val)=false ∧ lineSingle D (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val)=false
    let liftE (e : E) : {e : Fin N × Fin N // bad e} := ⟨e.val,e.property,(congrFun eqD _).trans (hacc' _ _ e.property),twice _ _⟩
    have embedding : Function.Injective liftE := by intro e f h;exact Subtype.ext (congrArg (fun z : {e : Fin N × Fin N // bad e} => z.val) h)
    have total := Fintype.card_le_of_injective liftE embedding
    let swap : E ≃ (Σ l : Fin N, {p : Fin N // I p l}) :=
      {toFun := fun e => ⟨e.val.2,e.val.1,e.property⟩,invFun := fun z => ⟨(z.2.val,z.1),z.2.property⟩,left_inv := fun _ => rfl,right_inv := fun _ => rfl}
    have mass : Fintype.card E=N*(q+1) := by rw [Fintype.card_congr swap,Fintype.card_sigma];simp [hcard']
    rw [mass] at total
    change Fintype.card {e : Fin N × Fin N // bad e} ≤ 24*D.size at bound
    have both := total.trans bound
    rw [sizeD] at both
    have positive : 0<C.size := by omega
    calc
      N*q ≤ N*(q+1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 24*(C'.size+1) := both
      _ ≤ 100*C.size := by omega
