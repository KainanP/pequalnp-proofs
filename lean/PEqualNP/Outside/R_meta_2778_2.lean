import Mathlib.Data.Fin.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2778_2
  (hshort : let s : List (BitVec 24) := [0, 16777215, 4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888, 16646144, 13339321];
    let g := fun (s : List (BitVec 24)) =>
    ((s.flatMap fun u => s.flatMap fun v => [u &&& v, u ||| v]).filter
      fun w => !s.contains w);
    (s ++ (g s).flatMap (fun a => a :: g (s ++ [a]))).contains 3428671 = false)
  (hsuffix : let s : List (BitVec 24) := [0, 16777215, 4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888, 16646144, 13339321];
    let g := fun (s : List (BitVec 24)) =>
    ((s.flatMap fun u => s.flatMap fun v => [u &&& v, u ||| v]).filter
      fun w => !s.contains w);
    ∀ a ∈ g s, ∀ b ∈ g (s ++ [a]),
    (b ∈ g s → a.toNat < b.toNat) → ∀ t : List (BitVec 24), t.length ≤ 12 →
    (∀ (i : Nat) (h : i < t.length), t[i] ∈ g (s ++ [a, b] ++ t.take i)) →
    (3428671 : BitVec 24) ∉ t) :
    have x1 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))]; ∀ (x2 : List (BitVec (24 : ℕ))), x2.length ≤ (14 : ℕ) → (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ x1 ++ List.take x4 x2 ∧ ∃ x6 ∈ x1 ++ List.take x4 x2, ∃ x7 ∈ x1 ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) → (3428671 : BitVec (24 : ℕ)) ∉ x1 ++ x2 := by
  let s : List (BitVec 24) := [0, 16777215, 4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888, 16646144, 13339321]
  let g := fun (s : List (BitVec 24)) =>
    ((s.flatMap fun u => s.flatMap fun v => [u &&& v, u ||| v]).filter
      fun w => !s.contains w)
  have gen (l : List (BitVec 24)) (x : BitVec 24) :
      x ∈ g l ↔ x ∉ l ∧ ∃ u ∈ l, ∃ v ∈ l, x = u &&& v ∨ x = u ||| v := by
    simp only [g, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact and_comm
  have eqgen (l m : List (BitVec 24)) (H : ∀ w, w ∈ l ↔ w ∈ m) (x) :
      x ∈ g l ↔ x ∈ g m := by
    simp only [gen, H]
  change (s ++ (g s).flatMap (fun a => a :: g (s ++ [a]))).contains 3428671 = false at hshort
  have hbase : (3428671 : BitVec 24) ∉ s ++ (g s).flatMap (fun a => a :: g (s ++ [a])) := by
    intro hm
    exact Bool.noConfusion ((List.contains_iff_mem.mpr hm).symm.trans hshort)
  have hzero : (3428671 : BitVec 24) ∉ s := fun h => hbase (List.mem_append_left _ h)
  have hone (a) (ha : a ∈ g s) : (3428671 : BitVec 24) ∉ a :: g (s ++ [a]) :=
    fun h => hbase (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, h⟩))
  dsimp only
  intro xs hlen steps
  have reach (i : Nat) (hi : i < xs.length) : xs[i] ∈ g (s ++ xs.take i) :=
    (gen _ _).2 (steps i hi)
  intro hout
  rcases List.mem_append.mp hout with hin | hin
  · exact hzero hin
  cases xs with
  | nil => simp at hin
  | cons a tl =>
    have ha : a ∈ g s := by
      have first := reach 0 (by simp)
      change a ∈ g (s ++ []) at first
      simpa only [List.append_nil] using first
    cases tl with
    | nil =>
      have e : (3428671 : BitVec 24) = a := List.mem_singleton.mp hin
      exact hone a ha (List.mem_cons.mpr (Or.inl e))
    | cons b t =>
      have hb : b ∈ g (s ++ [a]) := by
        have second := reach 1 (by simp)
        change b ∈ g (s ++ [a]) at second
        exact second
      have htail : (3428671 : BitVec 24) ∈ t := by
        rcases List.mem_cons.mp hin with ea | hin
        · exact False.elim (hone a ha (List.mem_cons.mpr (Or.inl ea)))
        rcases List.mem_cons.mp hin with eb | ht
        · exact False.elim (hone a ha (List.mem_cons.mpr (Or.inr (eb.symm ▸ hb))))
        exact ht
      have len : t.length ≤ 12 := by
        simp only [List.length_cons] at hlen
        omega
      have rt (i : Nat) (hi : i < t.length) : t[i] ∈ g (s ++ [a, b] ++ t.take i) := by
        have hh := reach (i+2) (by simpa using hi)
        simpa [List.append_assoc] using hh
      by_cases order : b ∈ g s → a.toNat < b.toNat
      · exact hsuffix a ha b hb order t len rt htail
      have hb0 : b ∈ g s := by by_contra hn; exact order (fun h => False.elim (hn h))
      have hab : b ≠ a := by
        intro e
        exact ((gen _ _).1 hb).1 (List.mem_append_right _ (List.mem_singleton.mpr e))
      have hba : b.toNat < a.toNat := by
        have hne : b.toNat ≠ a.toNat := fun e => hab (BitVec.eq_of_toNat_eq e)
        have hle : ¬ a.toNat < b.toNat := fun h => order (fun _ => h)
        omega
      have ha1 : a ∈ g (s ++ [b]) := by
        obtain ⟨hn, u, hu, v, hv, op⟩ := (gen _ _).1 ha
        refine (gen _ _).2 ⟨?_, u, List.mem_append_left _ hu, v, List.mem_append_left _ hv, op⟩
        simpa [Ne.symm hab] using hn
      apply hsuffix b hb0 a ha1 (fun _ => hba) t len _ htail
      intro i hi
      apply (eqgen (s ++ [a, b] ++ t.take i) (s ++ [b, a] ++ t.take i) _ _).mp (rt i hi)
      intro w
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      simp only [or_comm, or_left_comm, or_assoc]
