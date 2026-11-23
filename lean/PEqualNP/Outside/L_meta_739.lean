import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_739
open PEqualNP.CircuitLowerBounds

abbrev Edge (n : ℕ) (C : Circuit) (x y : ℕ) :=
  x < y ∧ ∃ j : Fin C.gates.length, y = n + j.val ∧ x ∈ (C.gates.get j).inputs
abbrev Reach (n : ℕ) (C : Circuit) := Relation.ReflTransGen (Edge n C)

def run {α : Type} (z : α) (F : GateOp → List α → α) (gs : List Gate) (xs : List α) :=
  gs.foldl (fun w g => w ++ [F g.op (g.inputs.map (fun i => w.getD i z))]) xs

theorem run_len {α} (z : α) (F) (gs : List Gate) (xs : List α) :
    (run z F gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run z F gs _).length = _
    rw [ih]
    simp
    omega

theorem run_prefix {α} (z : α) (F) (gs : List Gate) (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (run z F gs xs).getD i z = xs.getD i z := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run z F gs (xs ++ [_])).getD i z = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem run_gate {α} (z : α) (F) (gs : List Gate) (xs : List α) (j : Fin gs.length) :
    (run z F gs xs).getD (xs.length+j.val) z =
    F (gs.get j).op ((gs.get j).inputs.map (fun a =>
      if a < xs.length+j.val then (run z F gs xs).getD a z else z)) := by
  let pre := run z F (gs.take j.val) xs
  have hl : pre.length = xs.length + j.val := by
    simp [pre,run_len,Nat.min_eq_left j.isLt.le]
  let g := gs.get j
  let mid := pre ++ [F g.op (g.inputs.map fun a => pre.getD a z)]
  have whole : run z F gs xs = run z F (gs.drop (j.val+1)) mid := by
    have hh : gs = (gs.take j.val ++ [g]) ++ gs.drop (j.val+1) := by
      change gs = (gs.take j.val ++ [gs[j.val]]) ++ _
      rw [← List.take_succ_eq_append_getElem j.isLt, List.take_append_drop]
    conv_lhs => rw [hh]
    simp [mid,pre,run,List.foldl_append]
  have hmid : xs.length+j.val < mid.length := by simp [mid,hl]
  rw [whole,run_prefix _ _ _ _ _ hmid, ← hl]
  change (pre ++ [_]).getD pre.length z = _
  rw [show (pre ++ [F g.op (g.inputs.map fun a => pre.getD a z)]).getD pre.length z =
    F g.op (g.inputs.map fun a => pre.getD a z) by simp [List.getD]]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases ha : a < pre.length
  · rw [if_pos ha,run_prefix z F (gs.drop (j.val+1)) mid a (by simp [mid]; omega)]
    exact (List.getD_append _ _ _ _ ha).symm
  · rw [if_neg ha,List.getD_eq_default _ _ (by omega)]

noncomputable def kept (n : ℕ) (C : Circuit) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun j => Reach n C (n+j.val) C.output
noncomputable abbrev e (n : ℕ) (C : Circuit) := (kept n C).orderEmbOfFin rfl
noncomputable def addr (n : ℕ) (C : Circuit) (x : ℕ) : ℕ := by
  classical
  exact if x < n then x else if h : ∃ j, n + ((e n C) j).val = x
    then n + h.choose.val else n + (kept n C).card

theorem addr_in {n} {C : Circuit} {x : ℕ} (hx : x < n) : addr n C x = x := by
  simp [addr,hx]
theorem addr_gate (n : ℕ) (C : Circuit) (j : Fin (kept n C).card) :
    addr n C (n+((e n C) j).val) = n+j.val := by
  classical
  have H : ∃ i, n + ((e n C) i).val = n+((e n C) j).val := ⟨j,rfl⟩
  have h : H.choose = j := (e n C).injective (Fin.ext (Nat.add_left_cancel H.choose_spec))
  unfold addr
  rw [if_neg (by omega), dif_pos H, h]

def rwGate (a : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map a⟩
noncomputable def trim (n : ℕ) (C : Circuit) : Circuit :=
  ⟨List.ofFn (fun j => rwGate (addr n C) (C.gates.get ((e n C) j))),addr n C C.output⟩

theorem reach_kept {n} {C : Circuit} (j : Fin (kept n C).card) :
    Reach n C (n+((e n C) j).val) C.output := by
  classical
  have h := (kept n C).orderEmbOfFin_mem rfl j
  exact (Finset.mem_filter.mp h).2

theorem indexed {n} {C : Circuit} {j : Fin C.gates.length}
    (hr : Reach n C (n+j.val) C.output) : ∃ i, (e n C) i = j := by
  classical
  let a : (kept n C) := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩
  exact ⟨((kept n C).orderIsoOfFin rfl).symm a,
    congrArg Subtype.val (((kept n C).orderIsoOfFin rfl).apply_symm_apply a)⟩

noncomputable def ti {n} {C : Circuit} (j : Fin (kept n C).card) : Fin (trim n C).gates.length :=
  ⟨j.val,by simpa [trim] using j.isLt⟩

theorem get_ti {n} {C : Circuit} (j : Fin (kept n C).card) :
    (trim n C).gates.get (ti j) = rwGate (addr n C) (C.gates.get (e n C j)) := by
  simp [trim,ti,List.get_eq_getElem]

theorem raw_index {n} {C : Circuit} {a : ℕ} (hn : n ≤ a) (hv : a < n + C.gates.length)
    (hr : Reach n C a C.output) : ∃ i, n+((e n C) i).val = a := by
  let j : Fin C.gates.length := ⟨a-n,by omega⟩
  have hj : n+j.val=a := by dsimp [j]; omega
  obtain ⟨i,hi⟩ := indexed (j:=j) (hj ▸ hr)
  exact ⟨i,hi ▸ hj⟩

theorem future {n} {C : Circuit} (j : Fin (kept n C).card) {a : ℕ}
    (ha : n+((e n C) j).val ≤ a) : n+j.val ≤ addr n C a := by
  classical
  unfold addr
  rw [if_neg (by omega)]
  split
  · rename_i h
    have hh := h.choose_spec
    have hle : (e n C) j ≤ (e n C) h.choose := by change _ ≤ _ at ha; omega
    have := (e n C).le_iff_le.mp hle
    exact Nat.add_le_add_left this _
  · have := j.isLt
    omega

theorem past {n} {C : Circuit} (j : Fin (kept n C).card) {a : ℕ}
    (ha : a < n+((e n C) j).val) (hm : a ∈ (C.gates.get (e n C j)).inputs) :
    addr n C a < n+j.val := by
  by_cases hi : a < n
  · rw [addr_in hi]; omega
  · have ed : Edge n C a (n+((e n C) j).val) := ⟨ha,e n C j,rfl,hm⟩
    obtain ⟨i,hei⟩ := raw_index (Nat.le_of_not_gt hi) (by have := ((e n C) j).isLt; omega)
      ((reach_kept j).head ed)
    subst a
    rw [addr_gate]
    exact Nat.add_lt_add_left ((e n C).lt_iff_lt.mp (show (e n C) i < (e n C) j by
      exact Nat.lt_of_add_lt_add_left ha)) _

theorem liftEdge {n} {C : Circuit} {x y : ℕ} (he : Edge n C x y) (hy : Reach n C y C.output) :
    Edge n (trim n C) (addr n C x) (addr n C y) := by
  obtain ⟨hlt,j,rfl,hm⟩ := he
  obtain ⟨i,rfl⟩ := indexed (j:=j) hy
  rw [addr_gate]
  exact ⟨past i hlt hm,ti i,rfl,by rw [get_ti]; exact List.mem_map.mpr ⟨x,hm,rfl⟩⟩

theorem liftReach {n} {C : Circuit} {x} (h : Reach n C x C.output) :
    Reach n (trim n C) (addr n C x) (trim n C).output := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head e h ih => exact ih.head (liftEdge e h)

theorem liveTrim (n : ℕ) (C : Circuit) (j : Fin (trim n C).gates.length) :
    Reach n (trim n C) (n+j.val) (trim n C).output := by
  let i : Fin (kept n C).card := ⟨j.val,by simpa [trim] using j.isLt⟩
  have h := liftReach (reach_kept i)
  rw [addr_gate] at h
  exact h

theorem readTrim {α : Type} (z : α) (F : GateOp → List α → α) {n} (C : Circuit)
    (xs : List α) (hx : xs.length = n) :
    (run z F (trim n C).gates xs).getD (trim n C).output z =
    (run z F C.gates xs).getD C.output z := by
  let V (gs : List Gate) (i : ℕ) := (run z F gs xs).getD i z
  have eqGate (gs : List Gate) (i : Fin gs.length) : V gs (n+i.val) =
      F (gs.get i).op ((gs.get i).inputs.map (fun a => if a<n+i.val then V gs a else z)) :=
    by simpa only [V,hx] using run_gate z F gs xs i
  have orig (a : ℕ) (ha : a<n) : V (trim n C).gates a = V C.gates a := by
    simp only [V,run_prefix z F _ xs a (hx ▸ ha)]
  have corr (j : Fin (kept n C).card) : V (trim n C).gates (n+j.val) =
      V C.gates (n+((e n C) j).val) := by
    apply wellFounded_lt.induction j
    intro j ih
    change V (trim n C).gates (n+(ti j).val) = _
    rw [eqGate,eqGate C.gates,get_ti]
    simp only [rwGate,List.map_map,Function.comp_apply,ti]
    congr 1
    apply List.map_congr_left
    intro a ha
    change (if addr n C a < n+j.val then V (trim n C).gates (addr n C a) else z) =
      (if a < n+((e n C) j).val then V C.gates a else z)
    by_cases hp : a < n+((e n C) j).val
    · rw [if_pos hp, if_pos (past j hp ha)]
      by_cases hv : a < n
      · rw [addr_in hv]; exact orig a hv
      · have ed : Edge n C a (n+((e n C) j).val) := ⟨hp,e n C j,rfl,ha⟩
        obtain ⟨i,rfl⟩ := raw_index (Nat.le_of_not_gt hv) (by have := ((e n C) j).isLt; omega)
          ((reach_kept j).head ed)
        rw [addr_gate]
        exact ih i ((e n C).lt_iff_lt.mp (Nat.lt_of_add_lt_add_left hp))
    · rw [if_neg hp,if_neg (Nat.not_lt.mpr (future j (Nat.le_of_not_gt hp)))]
  change V (trim n C).gates (addr n C C.output) = V C.gates C.output
  by_cases hi : C.output < n
  · rw [addr_in hi]; exact orig _ hi
  · by_cases hv : C.output < n + C.gates.length
    · obtain ⟨i,he⟩ := raw_index (Nat.le_of_not_gt hi) hv (Relation.ReflTransGen.refl)
      rw [← he,addr_gate]; exact corr i
    · have hn : ¬ ∃ i, n+((e n C) i).val = C.output := by
        rintro ⟨i,h⟩; have := ((e n C) i).isLt; omega
      simp only [V,addr,if_neg hi,dif_neg hn]
      rw [List.getD_eq_default _ _ (by simp [run_len,trim,hx]),
        List.getD_eq_default _ _ (by simp [run_len,hx]; omega)]

theorem agree {n} (C : Circuit) (xs ys : List Bool) (hx : xs.length=n) (hy : ys.length=n)
    (hin : ∀ a < n, Reach n C a C.output → xs.getD a false = ys.getD a false) :
    C.eval xs = C.eval ys := by
  let V (xs : List Bool) (a : ℕ) := (run false GateOp.eval C.gates xs).getD a false
  have eqg (l : List Bool) (hl : l.length=n) (j : Fin C.gates.length) : V l (n+j.val) =
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun a => if a<n+j.val then V l a else false) := by
    simpa only [V,hl] using run_gate false GateOp.eval C.gates l j
  have A (a : ℕ) : Reach n C a C.output → V xs a = V ys a := by
    induction a using Nat.strong_induction_on with
    | ind a ih =>
      intro hr
      by_cases h : a<n
      · exact (run_prefix false GateOp.eval C.gates xs a (hx ▸ h)).trans
          ((hin a h hr).trans (run_prefix false GateOp.eval C.gates ys a (hy ▸ h)).symm)
      by_cases ha : a<n+C.gates.length
      · let j : Fin C.gates.length := ⟨a-n,by omega⟩
        have hj : n+j.val=a := by dsimp [j]; omega
        rw [← hj,eqg xs hx,eqg ys hy]
        congr 1
        apply List.map_congr_left
        intro t ht
        by_cases ht' : t < n+j.val
        · rw [if_pos ht',if_pos ht']
          have ed : Edge n C t a := ⟨hj ▸ ht',j,hj.symm,ht⟩
          exact ih t ed.1 (hr.head ed)
        · simp only [if_neg ht']
      · simp only [V,List.getD_eq_default _ _ (show (run false GateOp.eval C.gates xs).length ≤ a by
            rw [run_len,hx]; omega),List.getD_eq_default _ _ (show (run false GateOp.eval C.gates ys).length ≤ a by
            rw [run_len,hy]; omega)]
  exact A C.output .refl

theorem trimSize (n : ℕ) (C : Circuit) : (trim n C).size ≤ C.size := by
  simpa [trim,Circuit.size] using Finset.card_le_univ (kept n C)

theorem trimMono {n} {C : Circuit} (hm : IsMonotoneCircuit C) :
    IsMonotoneCircuit (trim n C) := by
  intro g hg
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
  exact hm (C.gates.get (e n C i)) (List.get_mem _ _)

theorem trimArity {n} {C : Circuit} (hm : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ g ∈ (trim n C).gates, g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hg
  simpa [rwGate] using hm _ (List.get_mem _ (e n C i))

def degOp (op : GateOp) (v : List ℕ) : ℕ :=
  @ite ℕ (op = GateOp.and) (lineDegreeGateOpDecEq _ _) v.sum (v.foldr max 0)

theorem trimDeg {n} (C : Circuit) (M : Finset ℕ) :
    (trim n C).lineDeg n M = C.lineDeg n M := by
  exact readTrim 0 degOp C ((List.range n).map fun a => if a ∈ M then 1 else 0) (by simp)

theorem trimEval {n} (C : Circuit) (x : List Bool) (h : x.length=n) :
    (trim n C).eval x = C.eval x :=
  readTrim false GateOp.eval C x h

end PEqualNP.Outside.L_meta_739

-- Binary gate normalization from the accepted L-meta-669.

namespace PEqualNP.Outside.L_meta_739



open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, le_refl _, rep_input ρ hρ⟩

lemma inv_final {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (gates : List Gate)
    (h : Inv ρ gates) :
    ∃ (gates' : List Gate) (r : ℕ → ℕ), (∀ g ∈ gates', Fan g) ∧ gates'.length ≤ gates.length ∧
      ∀ o : ℕ, (∃ x y : Fin n → Bool,
        (W gates (ρ x)).getD o false ≠ (W gates (ρ y)).getD o false) →
        ∀ x : Fin n → Bool, (W gates' x).getD (r o) false = (W gates (ρ x)).getD o false := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  have hsel : ∀ o : ℕ, ∃ j : ℕ,
      (∃ c : Bool, ∀ x : Fin n → Bool, (W gates (ρ x)).getD o false = c) ∨
      (∀ x : Fin n → Bool, (W new x).getD j false = (W gates (ρ x)).getD o false) := by
    intro o
    rcases hrep o with hc | ⟨j, _, hj⟩
    · exact ⟨0, Or.inl hc⟩
    · exact ⟨j, Or.inr hj⟩
  choose r hr using hsel
  refine ⟨new, r, hfan, hl, ?_⟩
  intro o hne x
  rcases hr o with ⟨c, hc⟩ | hj
  · obtain ⟨x1, y1, hxy⟩ := hne
    exact absurd ((hc x1).trans (hc y1).symm) hxy
  · exact hj x

theorem bin_normal : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) := by
  intro n gates T Z hg
  have hρ : ∀ i : Fin n,
      (∃ c : Bool, ∀ x : Fin n → Bool,
        (if i ∈ T then true else if i ∈ Z then false else x i) = c) ∨
      (∀ x : Fin n → Bool, (if i ∈ T then true else if i ∈ Z then false else x i) = x i) := by
    intro i
    by_cases h1 : i ∈ T
    · exact Or.inl ⟨true, fun x => by rw [if_pos h1]⟩
    · by_cases h2 : i ∈ Z
      · exact Or.inl ⟨false, fun x => by rw [if_neg h1, if_pos h2]⟩
      · exact Or.inr (fun x => by rw [if_neg h1, if_neg h2])
  exact inv_final (fun (x : Fin n → Bool) (i : Fin n) =>
    if i ∈ T then true else if i ∈ Z then false else x i) gates
    (inv_all _ hρ gates hg)


end PEqualNP.Outside.L_meta_739

namespace PEqualNP.Outside.L_meta_739
open PEqualNP.CircuitLowerBounds

def hot {n : ℕ} (p : Fin n) (q : Fin n) := decide (q=p)
def cold {n : ℕ} (_ : Fin n) := false
def weight {n : ℕ} (x : Fin n → Bool) := (Finset.univ.filter fun p => x p=true).card
theorem weight_hot {n} (p : Fin n) : weight (hot p) = 1 := by
  have h : Finset.univ.filter (fun q => hot p q = true) = {p} := by ext a; simp [hot]
  simp [weight,h]
theorem weight_cold (n : ℕ) : weight (@cold n) = 0 := by simp [weight,cold]

theorem line_agree_input {P L} (x : Fin P → Bool) (w : Fin L) (a : ℕ) (ha : a ≠ P+w.val) :
    (List.ofFn x ++ List.ofFn (hot w)).getD a false =
      (List.ofFn x ++ List.ofFn (@cold L)).getD a false := by
  by_cases h : a<P
  · rw [List.getD_append _ _ _ _ (by simpa using h),List.getD_append _ _ _ _ (by simpa using h)]
  · simp only [List.getD,List.getElem?_append_right (by simpa using Nat.le_of_not_gt h :
      (List.ofFn x).length ≤ a),List.length_ofFn,List.getElem?_ofFn]
    split
    · rename_i hh
      have ne : (⟨a-P,hh⟩ : Fin L) ≠ w := by
        intro he
        have he' := congrArg Fin.val he
        dsimp at he'
        omega
      simp [hot,cold,ne]
    · rfl

end PEqualNP.Outside.L_meta_739

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_739 in
theorem PEqualNP.Outside.L_meta_739 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true)))) → ∀ (P2 L2 k2 q2 : ℕ) (S2 : Fin L2 → Finset (Fin P2)) (C2 : PEqualNP.CircuitLowerBounds.Circuit), 1 ≤ k2 → 2 ≤ q2 → (∀ w2 : Fin L2, (S2 w2).card = q2) → (∀ w3 w4 : Fin L2, w3 ≠ w4 → (S2 w3 ∩ S2 w4).card ≤ 1) → (∀ (w5 : Fin L2) (p2 : Fin P2), p2 ∈ S2 w5 → ∃ u2 : Fin L2, p2 ∉ S2 u2) → PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C2 → (∀ g2 ∈ C2.gates, g2.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P2 + L2) (Finset.Ico P2 (P2 + L2)) C2 1 → (∀ (x2 : Fin P2 → Bool) (y2 : Fin L2 → Bool), (Finset.univ.filter (fun u3 : Fin L2 => y2 u3 = true)).card = 1 → (Finset.univ.filter (fun p3 : Fin P2 => x2 p3 = true)).card ≤ k2 → C2.eval (List.ofFn x2 ++ List.ofFn y2) = decide (∃ w6 : Fin L2, y2 w6 = true ∧ ∃ p4 ∈ S2 w6, x2 p4 = true)) → ∀ c2 : ℕ, c2 ≤ k2 → c2 + 1 ≤ q2 → L2 * c2 + L2 ≤ C2.size + 1 := by
  classical
  intro price extract P L k q S C hk hq hsize hdis hother hm ha hd hvalue c hck hcq
  let n := P+L
  let E := trim n C
  let N := Finset.univ.filter (fun w : Fin L => Reach n E (P+w.val) E.output)
  have Esize : E.size ≤ C.size := trimSize n C
  obtain ⟨D,T,o,dm,da,cost,rep⟩ := extract P L E N (trimMono hm) (trimArity ha)
    (by change (trim n C).lineDeg n _ ≤ 1; rw [trimDeg]; exact hd)
    (liveTrim n C) (by intro w; change w ∈ N ↔ Reach n E (P+w.val) E.output
                       simp only [N,Finset.mem_filter,Finset.mem_univ,true_and])
  let V (x : Fin P → Bool) (y : Fin L → Bool) := E.eval (List.ofFn x ++ List.ofFn y)
  let W (x : Fin P → Bool) (w : Fin L) := (D.wires (List.ofFn x)).getD (o w) false
  have test (x : Fin P → Bool) (w : Fin L) (hw : weight x ≤ k) :
      V x (hot w) = decide (∃ p ∈ S w, x p=true) := by
    have he := hvalue x (hot w) (weight_hot w) hw
    have hev := trimEval (n:=n) C (List.ofFn x ++ List.ofFn (hot w)) (by simp [n])
    exact hev.trans (by simpa [hot] using he)
  have repr (x : Fin P → Bool) (w : Fin L) :
      V x (hot w) = (V x cold || decide (w ∈ T ∨ W x w = true)) := by
    have hcold : (@cold L) = (fun _ : Fin L => false) := rfl
    simpa [V,hcold,hot,W] using rep x (hot w)
  have notT (w : Fin L) : w ∉ T := by
    intro h
    have a := test (@cold P) w (by rw [weight_cold]; omega)
    have b := repr (@cold P) w
    rw [a] at b
    simp [cold,h] at b
  have repr' (x : Fin P → Bool) (w : Fin L) :
      V x (hot w) = (V x cold || W x w) := by simpa [notT w] using repr x w
  have single (w : Fin L) (p : Fin P) : V (hot p) (hot w) = decide (p ∈ S w) := by
    simpa [hot] using test (hot p) w (by rw [weight_hot]; exact hk)
  have base (w : Fin L) (p : Fin P) (hp : p ∈ S w) : V (hot p) cold = false := by
    obtain ⟨u,hu⟩ := hother w p hp
    have hh := repr' (hot p) u
    rw [single] at hh
    simpa [hu] using (Bool.or_eq_false_iff.mp (by simpa [hu] using hh.symm)).1
  have mask (w : Fin L) (p : Fin P) : W (hot p) w = true ↔ p ∈ S w := by
    have h := repr' (hot p) w
    rw [single] at h
    by_cases hp : p ∈ S w
    · rw [base w p hp] at h
      simpa [hp] using h.symm
    · have hh : (V (hot p) cold || W (hot p) w) = false := by simpa [hp] using h.symm
      simp [hp,(Bool.or_eq_false_iff.mp hh).2]
  have sparse (w : Fin L) (x : Fin P → Bool) (hw : weight x ≤ k) (off : ∀ p ∈ S w, x p=false) :
      W x w = false := by
    have hh := repr' x w
    rw [test x w hw] at hh
    have no : ¬ ∃ p ∈ S w, x p=true := by rintro ⟨p,hp,h⟩; rw [off p hp] at h; contradiction
    exact (Bool.or_eq_false_iff.mp (show (V x cold || W x w) = false by simpa [no] using hh.symm)).2
  have point (w : Fin L) : (S w).Nonempty := Finset.card_pos.mp (by rw [hsize]; omega)
  have allN : N = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro w
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra no
    obtain ⟨p,hp⟩ := point w
    have ev : V (hot p) (hot w) = V (hot p) cold := agree E _ _ (by simp [n]) (by simp [n])
      (fun a _ hr => line_agree_input _ w a (fun he => no (he ▸ hr)))
    rw [single,base w p hp] at ev
    simp [hp] at ev
  obtain ⟨gs,r,hgs,hcount,hsim⟩ := bin_normal P D.gates ∅ ∅ (fun g hg => ⟨dm g hg,da g hg⟩)
  let B : Circuit := ⟨gs,0⟩
  have sim (w : Fin L) (x : Fin P → Bool) :
      (B.wires (List.ofFn x)).getD (r (o w)) false = W x w := by
    obtain ⟨p,hp⟩ := point w
    have h1 := (mask w p).mpr hp
    have h0 := sparse w (@cold P) (by rw [weight_cold]; omega) (by simp [cold])
    have hdiff : ∃ x y : Fin P → Bool, W x w ≠ W y w := ⟨hot p,cold,by rw [h1,h0]; decide⟩
    have hh := hsim (o w) (by simpa [W,Circuit.eval,Circuit.wires] using hdiff) x
    simpa [W,Circuit.eval,Circuit.wires,B] using hh
  have sumcost := price P L k S B (fun w => r (o w)) (fun _ => c) hdis
    (fun w => by rw [hsize]; exact hq) hgs
    (fun w p => (sim w (hot p)) ▸ mask w p)
    (fun w x hw hoff => (sim w x).trans (sparse w x hw hoff))
    (fun _ => hck) (fun w => by rw [hsize]; exact hcq)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at sumcost
  rw [allN,Finset.card_univ,Fintype.card_fin] at cost
  change L*c ≤ gs.length at sumcost
  change D.size + L ≤ E.size + 1 at cost
  change gs.length ≤ D.size at hcount
  omega
