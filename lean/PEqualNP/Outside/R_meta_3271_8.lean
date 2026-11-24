import Mathlib.Data.Fin.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3271_8
  (bridge :
    let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
    let flip := fun (x : Fin 9 → Bool) (i : Fin 9) => if i=0 then !(x 0) else x i
    let val := fun (p : List Gate) (g : Gate) (x : Fin 9 → Bool) => g.op.eval (g.inputs.map fun a => ((⟨p,0⟩ : Circuit).wires (List.ofFn x)).getD a false)
    let internal := fun (C : Circuit) => ∃ (p : List Gate) (g : Gate) (s : List Gate), C.gates = p ++ g::s ∧ 0 ∈ g.inputs ∧ (∃ a ∈ g.inputs, 9 ≤ a ∧ a < 9 + p.length) ∧ ∀ x, F x ≠ F (flip x) → val p g x ≠ val p g (flip x)
    ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
    (C.gates.filter fun z => z.inputs.contains 0).length ≤ 1 →
    (∀ x, C.eval (List.ofFn (flip x)) = F x) → internal C)
  (kernelCase :
    let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
    let flip := fun (x : Fin 9 → Bool) (i : Fin 9) => if i=0 then !(x 0) else x i
    let val := fun (p : List Gate) (g : Gate) (x : Fin 9 → Bool) => g.op.eval (g.inputs.map fun a => ((⟨p,0⟩ : Circuit).wires (List.ofFn x)).getD a false)
    ∀ (p : List Gate) (g : Gate) (s : List Gate) (o : Nat),
    (∀ z ∈ p++s, 0 ∉ z.inputs) → 0 ∈ g.inputs →
    (∃ a ∈ g.inputs, 9 ≤ a ∧ a < 9+p.length) → (∀ x, F x ≠ F (flip x) → val p g x ≠ val p g (flip x)) →
    FanInTwo (⟨p++g::s,o⟩ : Circuit) → p.length+s.length ≤ 13 →
    ∃ x, (⟨p++g::s,o⟩ : Circuit).eval (List.ofFn (flip x)) ≠ F x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn fun (x6 : Fin (9 : ℕ)) => if x6 = (0 : Fin (9 : ℕ)) then !x5 (0 : Fin (9 : ℕ)) else x5 x6) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → False := by
  let F := fun x : Fin 9 → Bool => [1,12,23,34,40,5,16,27,38,57,68,85].any (fun k : Nat => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
  let W := fun x : Fin 9 → Bool => List.ofFn (fun i : Fin 9 => if i=0 then !(x 0) else x i)
  intro C fan budget count hit
  have eq (x) : C.eval (W x) = F x := by
    rw [show C.eval (W x) = _ from hit x]
    dsimp [F,List.any]
    simp only [Bool.or_false,Bool.or_assoc]
    rfl
  obtain ⟨p,g,s,hgs,uses,inter,sens⟩ := bridge C fan budget count eq
  have no : ∀ z ∈ p++s, 0 ∉ z.inputs := by
    rw [hgs,List.filter_append,List.filter_cons_of_pos (p := fun z : Gate => z.inputs.contains 0) (List.contains_iff_mem.mpr uses),
      List.length_append,List.length_cons] at count
    have hp : (p.filter fun z : Gate => z.inputs.contains 0).length = 0 := by omega
    have hs : (s.filter fun z : Gate => z.inputs.contains 0).length = 0 := by omega
    intro z hz h0
    rcases List.mem_append.mp hz with old | old
    · have e := List.length_eq_zero_iff.mp hp
      have mem : z ∈ p.filter (fun y => y.inputs.contains 0) := List.mem_filter.mpr ⟨old,List.contains_iff_mem.mpr h0⟩
      simpa only [e,List.not_mem_nil] using mem
    · have e := List.length_eq_zero_iff.mp hs
      have mem : z ∈ s.filter (fun y => y.inputs.contains 0) := List.mem_filter.mpr ⟨old,List.contains_iff_mem.mpr h0⟩
      simpa only [e,List.not_mem_nil] using mem
  have ec : (⟨p++g::s,C.output⟩ : Circuit) = C := by cases C; simp_all
  have num : p.length+s.length ≤ 13 := by
    change C.gates.length ≤ 14 at budget
    rw [hgs,List.length_append,List.length_cons] at budget
    omega
  obtain ⟨x,miss⟩ := kernelCase p g s C.output no uses inter sens (ec.symm ▸ fan) num
  rw [ec] at miss
  exact miss (eq x)
