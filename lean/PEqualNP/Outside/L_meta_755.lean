import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755
open PEqualNP.MetaComplexity

def pairs : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(4,5)]
def rel (a b : Fin 6) := (a,b) ∈ pairs ∨ (b,a) ∈ pairs
def graph : SimpleGraph (Fin 6) where
  Adj := rel
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by unfold rel; decide⟩

def cut (a b x : Fin 6) : Bool := ([0,13,11,7,0,0,50,0,0,0,0,0,52,0,0,0,0,0,56,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,47,0] : List ℕ)[a.val*6+b.val]!.testBit x.val

set_option synthInstance.maxSize 20000 in
theorem validCuts : ∀ a b, rel a b → cut a b a = true ∧ cut a b b = false ∧
    ∀ u v, rel u v → ¬(u=a ∧ v=b ∨ u=b ∧ v=a) → cut a b u = cut a b v := by
  unfold rel
  decide +kernel

theorem acyclic : graph.IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro a b hab
  apply SimpleGraph.isBridge_iff.mpr
  intro r
  obtain ⟨ha,hb,h⟩ := validCuts a b hab
  have prop {j} (reach : (graph.deleteEdges {s(a,b)}).Reachable a j) : cut a b j = true := by
    have rt := (SimpleGraph.reachable_iff_reflTransGen _ _).mp reach
    clear reach
    induction rt with
    | refl => exact ha
    | tail _ e ih =>
      have hh := SimpleGraph.deleteEdges_adj.mp e
      exact (h _ _ hh.1 (fun hp => hh.2 (Set.mem_singleton_iff.mpr (Sym2.eq_iff.mpr hp)))).symm.trans ih
  have hx := prop r
  rw [hb] at hx
  contradiction

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem bound (s : ℕ) : HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  letI : DecidableRel graph.Adj := fun a b => inferInstanceAs (Decidable ((a,b) ∈ pairs ∨ (b,a) ∈ pairs))
  let T : Finset (Fin 6) := {0,4}
  have gedges : graph.edgeFinset.card = 4 := by decide
  have hcover : ∀ i j, graph.Adj i j → i ∈ T ∨ j ∈ T := by decide
  have hmin : ∀ A : Finset (Fin 6), (∀ i j, graph.Adj i j → i ∈ A ∨ j ∈ A) → 2 ≤ A.card := by decide
  have hnon : ∃ i j, graph.Adj i j := by decide
  have funEq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) =
      (fun x => decide (∃ i j, graph.Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    revert x
    decide
  rw [funEq]
  constructor
  · intro h
    have hh := L104 6 2 s graph acyclic hnon hmin h
    rw [gedges] at hh
    omega
  · intro h
    obtain ⟨C,hf,hc,hev⟩ := L105 6 graph T hnon hcover
    refine ⟨C,hf,?_,hev⟩
    have ht : T.card = 2 := by decide
    rw [ht,gedges] at hc
    omega
end PEqualNP.Outside.L_meta_755

theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := PEqualNP.Outside.L_meta_755.bound
