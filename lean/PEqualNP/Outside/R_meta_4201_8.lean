import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4201_8
  (normal : ∀ (n : Nat) (C : Circuit), Monotone2 C →
    let test := fun (w : List Bool) (s : Finset Nat) => decide (∀ i∈s,w.getD i false=true)
    let result := fun (P : List (Finset Nat × Finset Nat)) (s : Finset Nat) (x : List Bool) =>
      test (P.foldl (fun w r => w++[test w r.1 || test w r.2]) (x++[false])) s
    ∃ (P : List (Finset Nat × Finset Nat)) (s : Finset Nat),
      P.length=C.gates.countP (fun g : Gate => GateOp.casesOn g.op false true false (fun _ => false) false) ∧ (∀ j r, P[j]?=some r → ∀ i∈r.1∪r.2, i<n+1+j) ∧ (∀i∈s,i<n+1+P.length) ∧
      ∀ x : Fin n→Bool, C.eval (List.ofFn x)=result P s (List.ofFn x))
  (short : ∀ (P : List (Finset Nat × Finset Nat)) (s : Finset Nat), P.length≤103 →
    (∀ j r, P[j]?=some r → ∀ i∈r.1∪r.2, i<42+1+j) → (∀i∈s,i<43+P.length) →
    let test := fun (w : List Bool) (s : Finset Nat) => decide (∀ i∈s,w.getD i false=true)
    let result := fun (P : List (Finset Nat × Finset Nat)) (s : Finset Nat) (x : List Bool) =>
      test (P.foldl (fun w r => w++[test w r.1 || test w r.2]) (x++[false])) s
    ∃ x : Fin 42→Bool, ¬ (result P s (List.ofFn x)=true ↔ (∃ a b : Fin 42, (a.val<21 ∧ 21≤b.val ∧ (b.val+21-a.val) % 21∈([0,5,7,17,20] : List Nat)) ∧ x a=true ∧ x b=true))) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x4.op Bool.false Bool.true Bool.false (fun (x5 : ℕ) => Bool.false) Bool.false) x1.gates := by
  intro C mono correct
  obtain ⟨P,s,sz,wf,out,eval⟩ := normal 42 C mono
  rw [←sz]
  by_contra! bad
  have budget : P.length≤103 := by omega
  obtain ⟨x,miss⟩ := short P s budget wf out
  exact miss ((eval x) ▸ correct x)
