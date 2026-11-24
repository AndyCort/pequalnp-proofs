import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3172
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def adjMask (i : Nat) : Nat := [50,69,138,276,9,385,258,36,104].getD i 0
def firstRemNb (free o i : Nat) : Nat :=
  ((List.range 9).find? (fun j => free.testBit j && (adjMask i).testBit j && (o &&& adjMask j == 0))).getD 0
def colPairs (free o s : Nat) : List (Sig × Row × Row) :=
  (selected s).map fun (i,a) =>
    if o &&& adjMask i != 0 then (a,0,Fin.ofNat 512 (1 <<< i))
    else
      let nb := firstRemNb free o i
      (a,Fin.ofNat 512 (1 <<< nb),Fin.ofNat 512 ((1 <<< nb) ||| (1 <<< i)))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := colPairs free o s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := colPairs free o s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  pools.any (fun p => scalarPoolCut p k rest op) || (links (keySet ws)).any (sameWords ws)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

def hashcombl9 (i : Nat) : Nat := 0x180
def hashcombl10 (i : Nat) : Nat := 0x980000d109b03d000051820000304da0322085902f0000e01f00000000d06900000000a04a000000004031e000900ad0260000c06b200c00000000b086000051980000908e0066000010360000719ef05b0000e09bd931a196e07500000000000040961058611200006038f06d1041c092a101a07820270000602a301b000000000000235360190000010450470000300e000080600000d0050000a012f08f0000012f000010131054319b501e585f607e0000501c000010350000f03ad062c0100000000070300000304bd03c00000000005070950000205ac930d0874082f08000000000c045000021810000703e00000000014000004051b00d40230000717ae09f6079d074409c0000600f00680000d05ea07d00000000e1759083403380465043905341948102006520730000506ee0a08127802c0000e042d091b19a0000102e200260880000209d301db00bb07a801a216d111c906c9059a0080000a057113e20815018317b000020440000e025000000007028f0945029d06ac01740670000304f0000802bc039b01100000000000000000000904eb090602d408b70096084817fc05d6037a11b9006c09a50014064f09940498157a022907040040000e0890000d195b142f03f0020419fe16cb09311634076b0403056a09ee021107cd00350613034104cb0524130808ac05f0097e162c055d063911d2188c015419c408d00000000413b0000208cf07b0000a0719072a0774016805cc048f014c07f906f90240000f0070000e03b0000000008b04b0c00400450c110c48816629b183012018007006182054a406c031d0003c07c20810c2
def hashcombl11 (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0xc000000d01ad000007046200000f02270000000000603daf07d0b098c00000802ec603f641115000000000060506003159046eba12530334b026b014e700000f09772046dd13262092861642b084c919db3082d1944f00000f101b00000903f100000f07635051bd0398b0921500eec1840714c9003d200185a18ac009d340721404c8b9075d03c02063d00550e110800000007647121d4024290255607526076dd26260000000000007d6000005382bd14c8109a110685f06cf000000e0004021801010f1000230a100b0405000e01020e01070401190004052101000800110c00000701001200000e032e03040206010800000f03060018042b00000f00050b0702060026130e001a0208030a0211000b030d0c0300003f47011e010105004400010106030005150e030d0002082c010b000425042816070c0528000a030029060b26040000010034020202080d0402000617120b0503000300190304080d01000e02029201000a3800050206000a010304181200020306201d0017152107051b0118010007001a01130e0e1710000200000805061824040509000000293a0e031c000a0700080400260201000013000c0509060403020010000500050200090010080b072b02010701051b000b0205000112010002080a0329032a010900021e0f150625000046000003020741060700030217161807061010010d020003030401350a0200050801031e010701012e080617000007100008010502000f031d18090207030a05050b20060007040128032600010700100a0400040000090001110d0234000c0225000302000b101c131d1b000010012301010b010c1512000902061801100300112900050600720407020300032619011c04013304000003000f281905191301090201010510010101001d1b190a140101010300060b0030030209020a16001200051000000004004505000e1120052e100009040005011c1532070100010801000702001a040306061801230613050309000f13090100090524170405040005520412000312130e02031c040301031100090905000304010002000001020c1802020000060303010a04010e00000101010300060b2e14220013021e0004050407010201031e12030c0b030601090c001612071f0311091a01030002120002071203060500040900001f0300010414010003070a32012e0106010b0007030f080302010703110002002e032c0001160b011f01000d18000c061f080a040c03000a06120b02010d000e0100220f17140013011d0a03000f04010105000a054205010b07040001050600120000023b000a08000e010a0913040d2e110f01010205024d0208230b000006170002000960120501010003020019180011000e0d0701010101070919040700030411030b08140800020604010909 else (if i<2 then 0x400bc00000601397043b8028fc166300000000dc0000050065f0484b1344f0780204f4d10fb5071ac03dc409e5d088a000005024400000c032dd08dd0000000000801a1f138661761b07330000000000005dbb069be00dea03b1b109e2082f00000c060f000008038200000310a0102cf00000f08fdd03a5201b900000909bbc0104701413073b00000c01ac9089ad04a5419bf000000000000000d019930613417568057070481102952023b00000000003197b6050c203684083060846104ab41088d06db1090d003d940414b154de149b00000506a97049e00000d17ba00000c0428702540000000000000005150c00000b071fb05144092a4079450238701c53013c6177d205d7b02683003000865300baf098800000000000000000000f09e9f030b601cf00000518834186de0312000001098a00000b176f3170ea03d15084b318e9000007044300000a086bc084d2909000000d00c60000080446007aea041f00000819d8208fb3083ab01b200000000000134c0000000000a078a00000000a800000602bb00000809f07097d100dda08b6003a3ab925314a540474000000000000000502cd108ba206ee7013d000009097980924711c1207281033e30990000009177c1114d6b5010000000000803deb011e40779d9634a149700000f1342d0848e00fc2b50480409208a400000000007161d202da0000000000d02ce384fa209aa00000c057bc121680710b0714400b71011f909c0d0245306ef0000010890245520000010138801a2f0916e054bf037c000000000000000505000000080049601de000000000000000e062400000101b08111600000000000000010895403cc39231000000000040619203ff00000e14b1a09ab000000000060109000000000090080000004042a000000000000000000003090ef0229a082600000d03b3a02fed01a7000006086c00000100f000000c05684136e00000d0452500852086400000a15c245152000000000060496a1208f0391505e500000000004184a000000000000000000002264700000c038f0000063832e03830000000000202c039650804bcf04adb05150000020968802f8802ff908d7408c1307ac811bc602f9d19d6217eea04d6d18e2a094ea07b9505e2705f13075db06630000050600002c49050500000303a7006d1807eda046fdb552c050e20346800a540771c177bd1178e025ac09078057560094000005136c50841107a1e05919070220106f01033086d0080600000d09d2b153bb98301083bf11a6000621931410262108983022db01f151780a186f00000d014200000e01205120400000d263200000202d14135c70040f08630000000000c0128000009028700000a19b900033000009069a00000a182440703d015f000000818e0000060042f02b8c138400000f0 else 0x4d2618d4000009177590074000000000000000c08f10000030700902f2000000000000000b07440000000000309b3000008175f1053a0000040913d04dd71650000002137c70705a06a8303fce0922f08a6905b600000315720000000000a0430703e2f0555d07693055700000000000058f703c94156f415bce056b000009017900000205ad00000000006065e907d8019e3000008022ce141a20795b197a6153db01e0609af00000000000012660318205a4000000000000000d18e80081d014c0b088100000603db306c700000f03525132b2144a7002fa0351209cdb9922d0790d1927b19cbc0405008dba0046e09a60000000000d048a902b2d04edd03e9408b00000000000208dae0566715a700000207c7117e34001aa073af090970993403ab00000808e7e04809182b2001000000306cd8101650161d042e2046b405432181b700be602745150e304cd5119db090400000e1929409f500000504f900000000000000000000301c8015084072b80432400d7000006142800000607be00111d097ac166da089f00000d1647000000000010953f08f3818d510948809b8007911056f00000c198be0270b01f8502a7907c30000030354e017c72629418b030131c050b0000000000000002175900000a05fd00000708a8100070000091058000002016b9030a00000c094b0000000000301373094ca1334e00b4e1773707476145f0016f100e5a10598018ec03cda036bf04408060af35db20640e085df00aef040eb06a5c19e260202d110c1043e00813a089d00000100d3d04c5917fe804d8e0173508d4e0730d0307000a03053000000e00cbe089cd008ff019a4197e319acea303e0699c0607508bd2113200000e12aca175d3050d602e8f07fc0000090569006fd1041a0000061566419e70000000000b0324e076ac02d400000506410000090377b1724c085b5011c0000038625f04ebd07fb508d20000010802c087a807a56060c131321070c709b90000000000904249132900000304151070f000005047f5863ac04a23150a208b919510305d9010c95060b0000000000205b0000000000000000508360081c0000070737d093ca09c7e01bbf01b4d081f318c13108d00000c06cc5087c0000080366a163a00000c0177b1881b00a9301afb08eb1076b0000010176005ee00000a01ddb093100000905f51064a719f5e040d4076ea177a703ad4059500000000004059300108419cec127ce158761644000000000000000e014ce0017806fe000005048900000e1848a07c2895d6f9478c0463004f28092dc19da101f700000901b600000706216038e1067a40674f066b703f400000f09a70000000000b180c714835055f3111400000805cfc18149039000000211a200000a0920e14ea609ec0000000000f09ae00000b0743000000000)) else (if i<4 then 0xdd0000000000000b9b096e302b5c023dd0152c17863018d00000d074f0000000000000000000000000000005086e000001075900000f11b7000000000000000b02c26163390343606e03045b6097400000d065ce159500305e14e4107e9b0540d02d2000007052010519902e6c029800000e00d84049900347205e1b07e800000306692943890420d094d6062e902c6f002b00000604f1000000082a0000000000000000017800000b07e1094e2f0235684fc0000000000a018600000900b2d028b0041c6035c70704309ce1061bc04cbb08a0601ae8118000000000000000000000d10bf00000306e80000000000c13770000000000d1445b183e010a2208c7111dda056d00000919850000000000c08f6d178200000f016d107019140bc9413f047ef0256d014950893000009085cf01a000000416c980827b00df00000000000000070075218b3d03ec40450e0331b0962500e370857600f17018a0000000000d05110000000000214e341034119d1d134900000103df90338604b9704977085fc09110000000000905d0013d25191420008b03ee00000a14dc4033701612807240000050308000002097e00000800a7517adb02ee88470704bf001d831801c06dc90360517621092c119881105d103213156900000c02c90021b40634c0213317965037fb074bd17eb00000303bda10f8a066e7009a907980000000713a08333101c30423219eac083d8186e516ce406a7f013b907d300000601659062d409c1909d76079e0000030309102ccf0666a188500000f013600000e00b0308820000060695d07eab067270950a947580401b07e0a005000000406ac69076809c2d0124308cf00000104068024e0000000000c19e400000082e7314b6d033c90718d17795010740901b000300000a0248d09a2f09b5006c53090bf08d3d1945d175b9050100000693b37040480792b016600000000002101300000e1433006d4d045eb07c1602a100000208f8a047d603c8208c21079b707ce0000000000000000000000000804a1c055a00000d04dc406b300000000008018180597000005149800000304ae2923e01557c099c000000000000435b0100413c961827000005099400000000860000020983a072c715af002e2508a5a05b370902d083cd091ce085830375718b48067dd010f00000107818062501470e108b919b8907ba800ca501fa1178a5096f0000051735f09b4000000000021066700d4f1209e80e200000000005068f108ca102d6000005006e000000073600000c04fa207860000000000307250000050797200d6116cb00000c08b8000000000000000000000000000000000001005d714a6b04e20000020658f02d89095a109c5e927100000000009323e007b1105252015e107e20140df0623c036280301d0089f0947f0431806095 else (if i<5 then 0x507497029c514b9824e8f19790163d0000070207c00ed00688f059ec04c7a093a000005067560875a95e7c03c4000a6607ff4187d705f850211004fb000000000000000718900b45700000606480000090341217668009100000a11a7a186cc00abb036dd0101403943080b106f4808c37143b0000020385000000000000000801a800000806d94005200000e0654f082e809ca00000506b96076c6068bf0069705e8a98220000040628802f7d039a101e6702842170b317ccc08b7d01c1d088ec01d2a04077014d000005073c70535000000000020441309ef701fce01e2c0411509c8a039200000b149a808096027ea07742055dd05d63032a0000041283705d1400c2905d4d01caf067b909b123362302e0895ce2160e20001a0564014f1909e8e1151906d0306a0618a6b9500d9236205f6d0731709d9100c100000b09de317b0907f2708a3807208189b00000d1287b05d2000004052b8038700715e06b800000b0886b098600000300b1e09959069de04cf307b7e10097019c506af200684184c414ce0084200000d17854059cb078700000019d93515be02b6218efb081b000000046c303d850014000006099a000004057e000004054f00000000000000000000003c70000000000305a000000000000020890234d06a400000000000000020221a05c700000e14fdf069cd052900000900480000000000000008001500000e010d90832400c49064d000002000ae137400000e0866a00832026f000009058e605f9e0559617927028300000b09640000000000304ef00000a00368004a0000000000f043400000a13d100507705e730722207c800000319812067900000b04b73000b891d07059fb9396b05a7f037bea1d700000000000000020746e096a3035ab03e8d04e050396200eb0082921629004d100000803400000000000000000000010230f030200000d866600000e19c6000000000030214d16680000000000001640000000000007c93087d6048b00000000005043cd043300000802e3104720000000000d0303a056300000803a8100cd60182e1571b08963078e000000000080187406df507dff07e50000000000a09fd00132593165082b41520000000000000000602e4002b9fb4f100000401d400000606e40000010707508e2b15ec014d000000e0170701a3e18f0819b5f11050000011784604f600542302cb0000091729400bfa0510402ed500247063750071106d5007abb00b5302eb111f9706d6601711007ab01ba10372a0818515c800000605c24093240686e11aa20915a00ccc175a70696d017b203c50000000000c1012b18ed30761504982031af06c49023fd02a5808efb0860e080e919e910805f186900000706e200000c056c000003099910276a061ac116d7079d705c62020f419f7506c8d0370e09 else 0x60d5143d600d5a07af00000d012b903d06080a20934407d550548b0521a00198077650243000002073d409c9106222133d00000a08e350587798c500000e09d5b0586000009184d000003141800000000000000042944b026e01889b00210000000000300d110296908cd2109d70693608aa5094911776808e931254804da008de000000000000000b17ec2078d901efd051d81946e010e00000e120600000611b300000b1465a04f800000804a361426c01550000049648507e6402047045a605768019000000904c0d02240000040491000000000000000b08cb505dd00000195eab9637000002052760649519476154b00000e0353d03f200000000001099230326c15c4007b5702a2000005013e008073099f107b8000000000000000c003a818059045600000000007073950554000000000020889401f3000000000000000e172700000b147a0000019636a0269301722902ba02a84053ec18c950837000f4202f4d064e00000802339008df03a400000304b1b06c300000f174a7064f0018c7022880317b06bbd0544b169860292e05fe4091000000f13ce703b9419ab80413294fe91333801e1b135be0316a0153d04b4f00574099b00000e05ccd04f3d15a6f034d414c5318a7b063239639b1667108e6e11c0809ed11552008430185c701e7b04db8114a908fa70588919a021855e0965d09d6300470000049503606fb1159e201ea905fab047a417701003f200041086790426801059049cf041d305b5e14acd015a9171500000518715913900000902ab00000a133a0000010044201b14939c0000000000d002500000003f09054d000007091700000d03d7b05b40000000205000007153f0000000000815e8000002027c0000071414a17b1110f2000004050f818e300000e05e6b09c400000a03c6504767031fa0573f02af403afe023200000e104f0000000000604d5e184bd05d5709cb00000a04850088db01e80000000000f077cd0206806e7e03bb5087e000004068ac025d6093800000d100b809f3f003100000c07a300000404ea1140a000004057400000a033600000f0883c01cb8136f901f64070df09a500000c0534000000000000000a04be6087f000001034400000b03677072e405520000000000206e5000001106890677609dff0064b025c00000709cc3070aa24651009e00000c05e40135e000002032591611e028d00000f055c00000f084e00000109eb600c7a923f2000fd022a00000a078c104d40000020839714c4203a6d0727405ec6096080821000fe407627027a202dd6a4ed7025320250a088fc04c9000006004b2015630929e055e31989002de00680401eb00000a07e70000000000c262500000602a4000000000000000f1332e19d3d00a3409805087900000d0644000008172ec08d9e01d3d01b8208d1))) else (if i<9 then (if i<7 then 0x3c09fb9054e2043990630c02a0409be604fec05df2017a315735191ad05b92025e20851607b35946f41582400870068ca0868f065300753908922183900000512ab0000000000b06ea000000000095125b00843068d0000000000d118e308d85069f20323c07de100bb009352077030615500ff700613064680277e0523c24fc303490000030751000002048c4a154d052f8013030598000000052a907d1d01c400000105f2295e3f03762095b00328a0991b094070122617020000040059e188c302b300000205bce077300000619ecf15fbe092f70816c08e1208c8f0664a1193000000000000000e0473303cf6061200000c13220000000000e05eba009f00000a062b00000b03e5000007029d000002098bc007b208123092700000000007080cf0817d1570000007073ee128f607a4c03e700000808100000000000000003003e00000000000046a00000c3076f19f400000101e37034e0079f21536c144850281000008075a00930406140000030425e0286f00414090c0000000000c0222803a070218702ea414b4c072900000409667061dc0364c07410000000000e0330f16b700000000000000000000000000000000000000007022e000000000031934c071c7058200000000000000000000000000000000000f05d8000003156500000000003051e0000000000c095500000000000000000000006c0508b300000208a2809ea7077e8033b802640000000000000000000000000b080d20478109a440247e09ee316268075c502bc000000000074153016580000000000000006382f00000f06e6b06051061100000207cd0003c103b8913cb4079990862597e6d18685022300000000005161000000807d7000000000070095807ecd00390000000000b002d40365000006021fe22e13048600000401b7800708053100000a0494000003127b105cb0000000000804c10000071253600c8f176be01ecb061e819996006fd00110000000000302795177700000303d55094600000c04838066c319eb40273c04b03056a00000f011700000b04602038bf05af5164ec049f408040000000000000004081140522000008044a903b6000000000000000d0690f0028000000000000000000000031cc08d500000a151de00760000060464e939ba0900b045d207650000080216307bd00000702a6907580000000000804bb806617069260561519190098d114a40016c0000000000e03a90000000000f847a0000020448896512960830691b05b1805bb5144b0157e00000304083049bd03fa00000c021e8092e00000f0378515fc803ba601c7f067e008a79051a703f5f11c5000006074d000006019610631000001153e2054aa06d85964a0067c1096db032b0000000000d02a3a135800000c077de068100000b173000000e06ae0000000000f0 else (if i<8 then 0x60310438b078310961903eba07f3107dd302dc00000804c6000004007eb0299f05853023a800a1e04873008a20445b0175506f1104ffb0539a05a2b07a8000002006c2000200000e00bd817ed0030f500c5f07d4c015d8120b207f7014f5f123c8087bd14bae095ce0209c090f31617514e8101c3c121c219a9b03fd9127f0000000000a1789f033ab02171042bb414eb114f1093e806a3a053bd17b9000000000000000e081a6002300000507bc0000090989d0358000000000000000f039300000c04cc209fe89931a05b700000d07080000000000207a0300530031d300d9907ccf339ed03fb206be507d90000000000e01f51064300000b1898000001165c3022ba03740000000000000001078f00000a056e00000f0099000000000000000000000000000000315d0000000000000000d0512000000000000000718c400000c098ef08ce206368094400000000001097b00000605d3207f860742502ef00051d0239007cf6025b30300b099dc16a2000008063fd16d190803b043f406f3b076f215b1203beb02c8906b63137501826f00e8e0150105f700000410574033f70013a02db102fa417cd00000b06ab709ba304f50000000000407bb700e1d089b00000e081e00000503e4204e600000904ecf0219a093d3040f00000a0620001a9e16592093b5015b5041953651d04922042c603e69168ae190c90926a020af075400000e05710124100000b08f5d0537f08e4f136500000e06de000001091eb03c37088be0314804aa104e4b134b00000e0188e08012039e30650008abb052d51006718af495d7215c3508b5118ca009a0c08b4e04a73116b109bcc06f270096302bd916166012fd06355982f108df91501a07f520959e0288312a8809370000054154107893008b11190a12007020b30237806715095120884c0844c09e26b54dc053300000b09544149600000005e9a01958091b009c300000000008112900000c06b200000f026500000000000000011087d06270000000000000000000000000c04a61028e00000d065a701da70356000000000000000102201014f000009023c8034ff07725075000000000000000000000b048890458301ee00000619d719172308733066840066807b2000001005f00026a152f501d1807b00000000000000000000000000f008200000700380000000000c057c0000060403e05490000070518902728044e20280000000000021751000007071b000004009b4005b009e040581102a9118c8500f20000000000000001047c30815000001003dc038900000a05f30062a800060040c4063ac14b301728f07feb06fae982ec05da2075bd0200e05ce604df206ba711ed005901a153db91ef0180603ca00000503bfe09f600000406aa607e3a0905009ad00000f01f9504d3e246a3035ee0852210a else 0xa33036cc846da036eb865cc011900000000003015100000908a9a067800000d02d30000000000203f300000b17780049a2040210386805f4601ceb163e1114eb02670000090183c06a6e01c2d07c610859b06fc1183600000202dfe153c80020606622005431159d04b50000000000e0380e015430078c006de05cd0000080726901479016e8045c6058b0923dd012a304ca503cec029f2032c5002c7037e601df108ed106984029a504c480502004001030cb07c5608ccf02bf609fcd0212e013a309e7b047900000a17c0105c8a02cad19f800000309f7e1834b024aa095f1001dc05c000000000004071db0819a04fc201d7111bb8070b6163b6a5176015c201b3909f2c511b93639e07e4205bf40455309bd00000a068ec15ba000002072d00000f10c5d04f06095200000403fe9091af0079a103640098208995094f900ac00000a0077204476096be18289020e305ac0000000000301ab809434946ed092be057a000001064b30602106c2e02ac9005e308ae5169b00000d0782a030eb148d9121100000000001073f1091430429f06f9000009134500000e35e7109a8c044d09643a191b00000f00a2f002a60289000000000000000910a1900d07029bc3090002b1505c99093f4036f1053cc097040465309c600000718744014ef05c400000302311016aa017e717746040bb017d202c1a06a2719cc910d9109f900000000000000000000000000000000000000000000000000400589025f008d600000807ef00000617877000020032100e0407480026398669a06820000000000f08b15088700000f0618d137070982504d0601e91077f0000000000002c5900e2709a30000070056e0461308ec0094a60874919c8909848001e000003000970855a0723000001001200226f04a9000cef09a97088041387db53f410c0d01fdf086ff0159e05b2000000000060919914ab312211142d610fe0003bb93ad5132f10908e05c180604000008091f000007071ef02d7600fd000009062f00000008ee507320000000000004e700000106d2b85dc0000000000408bf608bc8090300000c06c10000000000f059ba0629a186bf1002000004088c8053dd02d96063ef198ac09f800000503c100000605de209d8101f01198000000c18cef165bf1150000005165a103dd003732011b000007021cd25d8a052c1051f00000000000000000000004fd903713187500000e0490809d100000c01d05096cc0660c0266300fa00000902940000050475701298188d005bea0778218875a361717cec0526504667078b307f66963c9115b2024f0186560592502d5b05baf01be40381a054110355405c330055c034851339707f4004d9107c4f01486096310092e04a0c057df03047030db09db80345d001b401aaa1183b0115304f7802e5306708106a40996b)) else (if i<11 then (if i<10 then 0x7026d00000c08f7f00af800817054c0000000000b050900000a07ca00000c1825e041ee055b00000000000000000000c0589e04172007d000000000000000000007175e000000000000000000000000000000c18880000009832707aa3012e00000206c600000000000000000000000000000040971e008c00000506f8a1067a18db00000807cb00000a010ce08ff00000d0285000009101e506b700000b006000000000004074a202580000000000b0504e11ea00000301c0d08388175cc008850656c90b70000030719e02f5218eb3083e0000000000c08bb103b700000a026000000e079ca06bf00000d014a000000000000000000e700000d082800000000000155ad04b60000000000f19b4b1892b061000000808358009c111bf305a1c02f6c06e1f0453c059da174d3098fb114b806bd00000918c6006f70000000000a0350606678148a00000d0163e161f0000000000f03cb00000c164900000d051690442000000000010451e0384c01d6000006080ff0756a09750000080169e00b800000a048d1037af05f0108b20004f507960000000000607169014400000200b60000000000e04bd4063c208f9613cd906d35157ba01f49008e517954021ac024b60118f06ec000001082430775f0513109062183c005ff000000000000000f0333d08720000000000300aa805a63180a60113f03efd0240f09bf205ef6040a000000000010808c06ca106ce9004c703b2e02510000040987b0158b0444a0885d06010000000000f04c23095721352f028a4059a51820907660000080800000003132c4120140709800f500000902bed087081210807bf0000000000207a7403b400000703d6819aa50578806b44037d00000db566e014be050a401bf000008057900000f1838704d7807dae066ac02821085e00000911135047700000518371198600000c077a307a67021500000e01dc60363f0246d01d900000a0755c0114b137e80777f025240551000002000e00000305ab79635505654045440985e450400000e019d919e6000009089700000000009152a30856791cd0000000000000000000000000b05fc0000000000000000000098945b0313c0184d0978a06f5b07882198c00000b0342709b000000b02aa00000000000000000000a0225601b500000000005b428702011067fb3510d00f30000000000e09e4915a0a023ea0194f07f1904186863200000a03b0f0638000009105bd08fc700e6d08880000050278307f9902c30000030956000002066f0000000000f0981e000500000000000000000853103a16000c60319000000000000000000f810471b041000198a097f0000000000005604120500000702c7903a200000000000000000000f94fb0000010577700fb706da404b300000c065f00000b146d714 else 0x9670000000000d09cf00000e964ff0617b044b402fbb00f700000f019ea1104307a250536600635079a30767c05946169d00018303e0f13277048fa01257012dd08c4e09d00000000145f0651107d200000c08e00000090942b00e900000000001007200000601cd00000411880000000000303113134f60697e07454109fa09fa608c62018b0000000000409d4e001c906eb0000000000285e43162f00000000000000000000000009031e0000050524000000000000000333a0000009035f403ea2006b0027580583000000000000735e9507701a6c00e400000000005024d40135e066de018911187c06b54064c00000207eb618f60000000000001e4b0825619e02022f000004029ec09e30000000712802b4900d2a01f279831501680028c1034a00000606adf06a1d012310134d0596f16de9266720918802f000000d084780306000000000020327d09b2916c700000b010b00000505e3c06ff40297b047090102604def06160000050717102e79000de04e8a97e5aa13300000600da0863b0072a00000006bce85d2805eda1007000007014670192f039f10193000008023600000200ad703d4914fe9092310035b03ae602fd00000000006183d80584a17ac0000000000106081092500000602f12058a000009026c00000f1084f1202b863e304b8e00c300000000006108f0000000000104a8000008067370876608a1000008054600000706f00000030657d09987016000000905c5a1499001bd73172d044c806870000090067309ac009dc0000000000fb53e00000b150df08145095e40820000a450482806d7a013f1047b00000e0706701fed011031910a06e3a00f6811ac808fe000003051c013c8f160c00000f078500000714c600000609f100000a912600000d1222c18f8000000000000000000000000090936c0508e0834b05628027ba0449e02710000000000102ba50939083ceb19bc6127d50037618911057f00000606cb000004046700000a043d8091db08f2103aca0197000003089100000700f9701a4e019b00000b1350b101a0000050157c133800000000006083f000003031b9085ad0626204e9e064200000c05dc6019fb9585b0468000009042fc14b8301ed7105e902f3508c9f18fe00000201c9000004175700000815040000040849e03797033d00000a02fc00000f011df01670110651464d166e0000030191801dbd05a9e02575065d8339800000105a500133903e3816527009d5137a00000b188b0035df08add004d608612055300000c121a407ade19df101cc100ea403aae187240599608f4ca42140871e0293306765109ca086a303ed2054500000701a5125d250329000009005ad02b02045f00000110c360112b01e5505fb00000000000018fa0580a07dcf190d611c44072f1097c9027d008be5060e) else (if i<12 then 0x60121f024c9038c9001fa0369c063b00517c18020035bf183f309b64052e00854c166400000419cd91348007eeb050360437e011aa109a20397d012cd01bcf06849133f11284a12a7a147b808c030738606470000000000e068330093d1656d0969d0757a046900000000009069ed017400000c143cd0029d157fda3090000000000c0045904c3803b5507b6616e89061ce03f9913730127ed02d0000007075ef08782063340547a007c0000000000000007056780740504ce000003076880332909b7103573099e00000408e500000200348083100000406c9c03200000008946419de000009026100290e09f4909410017f60259000000000040840909331077ba00c93053f814caf0689804b290538a20e2895d5605ea100731033500000a02ad00000d15bec08af00000000009033900000410ff00000000003097300000802b7c007f306060000000000005cae020d00000f02e9800efc0027204214058c808ac9049d3847c000008042d0197db01d5a020cb074c00000101ffe021d00000608eac172d0000000000f119e0000000000303590000000000a1558000005039550457a137170734300970000000000000005010a00000b070e0000000000d04ac4041b106b010140b05bd10793b00434026a707b4719ddc058d209dad043ab032e81666000000000000000e089400000f074e205a86147c707db0000000000708dc000000000000000e364fe005c514c7000000000000000a00b38034cc075f01654e03f7b095d41003e11a9b02e1700ec20645b170900000b04e3213415065bc0241e18c7503101002e31517f177ed061f0000000000a04ba9039d2039c407a900000907f000000605e00148b103d36016210143a06f6b08c550945317e800000c170d203c2c08d00000000000b082c0000030022b011600000000000000000000311090000010556f0639506590000081189102100000050422000000000000000010d600000000002034b00850a145b000009044fd055800000006b1a16e0000000000000000109e600000000000000000000319e10000070412408690006a805328038a0000080528500dbc1933e16ffa0495401277089e0000000000704270000030976f07c03069450291000000000000000a048e895df200cf00000d659e0036a00000f038db04ee81170905b8a19dc6062cd0912000000000000000c08e8000000000000000f93c3f02aef027f504e5000000000060361c02038039be120a000004948e60090e01fb00000819f6000003188e00000000000000000000000000000000000000000000000000514fa805aef06ed1121b0000000000a02493084f00000609581004ec01c629522000000000000000a09970000000000e076000000e065550823103220000000000a071100000c03bc7066500000f0 else 0x9180920652507fde11b00000000000000002084500000d117e603f8000003161a00000a04a400000000008087700000c032fd0399206e900000a0436905a3707fae105ad03e1804e1c0416f05aa611526153800000708f06049330972203887177fd04af000002084a2090ad07844194a20459c05728154cd11e080016e06dde15e6993e840822d09e10000))))
def hashcombl12 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0xa023000000c076de099e000005037b00000202ad9123800000b08096069160186e025710913208b810950e0800408a3a06be095caf045800000009cb60233919ff300174096cb05f8f07208087240978702d15168cc04f8e0144f0885a046820a09008b6e192be14c3d08acb005f3036cc094720435d05d4c09ba405f66167c914070000090962c09ce20826a067ee018390162219b090309308abf0339000002091ea00f800841f1185e08df60455601b4e071e70324105eaf079719544f02b260a1a0a0b00004c1f0441000501021202046f15030001070e00061b0e050f11350d021a07001b0106430100111502011f0001020d090032230e270005021b0431000100370102070f05000b000107010104010300180c060e023503460703000b00051a28010c1104021e050f020f8e0117040302000806090002460008090218000229b100003611010208101c052412160a010308610e17232a090a0001000000432004041f030c022d5e0c0600055c030802090603050f150a0144000a0b00050c07212700000003010b0808190a011a0f0041442d0500260a081c330414051d060a02031a021c1b2e0e093649071f03000302000200040202012d0903120201060f020e00051906052708020401140754351631282a01190f061215070202020206321535211d01002e111116041f2008020006090004050206000073070d0a011101080e06000a131a1e820012110c05350c5515040129000b0105130343000e02040300472500000100001d0a0105013b00110500040000131b0100010c01110101010f000200311015000603371454013a0431310c3e25072c0a1909040d0100000b050f090e07002b4301030002161707001d001b1119030e151004090304025b03020117250401000a3104000f03020a0c17300101071d030406080101030400020a010502000402022e1d1100000a1e00001205020018160f932400120a110e061c02030307101e185b012c030100090707020a021478040c000e04391b010b027d160201020800003300051a0b0409000c020d11000006061401140307000702020e3704021a15001705050e01065e391e001d07050c04040f0900140e0013080600010f0a05073210000b020101000c060504093c0c0c080403024e2b01003401af160748880200010603040000020b02000a1d030401013416110060071b04100101050e17012410010406250000010a0717031513081800220000081f101a000033080403243547020d1e170033151aa305080d0d2005040506122e0605204d000f00000d110a041b10102f002c0046033a02031f0044060800010900110203040002022b70026c0816120e0f051e1f06170004060a201a01000300010007030413010b2317010f070409020c482e030b01034b0800015c00 else 0x602b4a048aa0304d06aee115a703f5f0348d0684f08bf000004021761376f08a780a0591a1200000000000000070346e112b202b1c016100000213b6b153df02b700000d13f2c09cf201255044d401c3c14bc21504d02db00000e1178106fe504ab000005010de0357907956a574000000000000000b02c5e039f4182260174602cd1004e2070d0000000000b07a500000500aec02ce00000f075aa076e0000060764000003074e400a9a039800000701d20000041313e042ea0a226013c904d900000f90e4c061a00345b005a90989a140da0041d0a014152e60421e151ea048f917ba708cad91a1802c68036340a101005740776e05b6609793043e3177e00000000007195a000000000080316406cad0a0f30a23703d8309abd02a54080a906f2e05040052e3068cf11122095b00000506075007e00000106811064bc08cd117d2f961510364d00a8e015ba07d7a00ed903866131c0000000388f065be007fb002b703d6305e6d18a1609d8507a8f047e00000d0a1901099102bc204d870016b0659c061d00000704311140900000f0603901c5c06acf05d8703ac201e0c028f81605b1608507d5d00d0815c6d0497000000000060576117fe0000090693e07c2603f6a09d430706f0123c009900000820d9612a7503a400000216e1e0686a008fb0239b087e902c370622d0815a028511204b0580103b0e181600000618e03081b105f3a12bdf012ec05e25060d418a600000309e2803b1b182120427c0300f0204107ed1071a3030f904e390770e05209166780002a0707f09f77040a30283f069ff01e400252405812090970482f0919000104038e500db104e2f0396c064a8081f504de107a1e069ef031b107aca05f1c077bb01b5202c4c129e00000f03b35035980473a050050018803cbd08c5d0390b0563d097a813393040f0000000802d04e130932006fd902515030100000a02a0a03941934c60727e08e8e072d30894302a14014310308b04258091a00000004cf906a7204dcb02433077c31512c1956a03dff04c4a14df60a0c302c24005510430204f11086b905ed9190791061e14bb200bdb14b3000001018db08d56010400000c00cf001a5e05020000030645f0512000006016710969604dfa1a1b118b43006bb00fc00000c09396089f3073400000605540000000000b14f000642c12c000000000009861ce0632e01f42078c619f2a086e607c400000402aa000000000020920205ef00000f107000000001ad00000405d00000000000316b3a0760306efd0159101f50000000000607a700000c01a1f1779307f2901fb80078402c7a18bd00000000000000030982508f3d0690d12a8d094b502f6d0110012d4e05bee16d6e058230556d19400013350a1d0000021607c02b840263f0004b0921b0634e1379613eb5093b) else (if i<3 then 0x2403fe505c36b5875000a507e6606d51179cc083b902d4c03aae65a3d014fd0543408c3605df901e37133eb0489503bba17f550271d01840000000000c18e6e04e98058800000f00d800000a08f20000000000704e7f070fc07b2c02e19023f60185802ece02ed707bc303121093580247095e2314c031320116916053800000d042a70231306e10000031353b03b5608ea0178bb0378604e070083d03552079fc13fd502e41051060318000008180b41319807c1a13a840244e07cdc18af0124200000a09a57031fe10d7d047b712d860191d00d9904db10302606c4c0a2800000306c3f02ab403b6f048cf022b00000000008053b000858130ba07f900058001f1809610000000000a0a1ba093611545510cf410a200000f159900000410e1309c9a08afe0128d0619617892138e00000c032fd056ba06f300000b0535e0305111d650a29806e7509bdc027f903e6207ba0053e2028b5044c318f70009d6077150135c16c250281401089053740817c05774027dc055a705c790963c11b700814a03c8e19e020717c040c0002261159c044761930413e9000002197b000002060ef1929e041400000108f5a0610104a8e012cb0796f111b804a6803401061b206a6505b5302e8c09670000051966a044300000307b350007f09be40423903bc4011810593819e1900d441067a056e419e2907570000080668406eb6021e405c23109cc17f200000c12e681209000002120850296609055063e104b8f072c3001b50330f160cd04226158960054b05dca047d6065dd75a3a03c2904874089b713f40000031216d176a704c30034400000e03ff205b290005d1870014ab00000f09aa40624501965006a601d900000303c079498b0660002080000000895c016b31637008be9029b91345009a400000c0a1500000411ced089c00000a017a21710000006033390a18e05a251402d000d00000000000000000000190ab0000030662a0353000005023e000000000000000103620000000000e094c208a5b04c860893705abc159f000005189e00000000009082e00000809d30000010216a10a5100b6d06f6a1364d192400000b06460000000000d0851203b70000000000208ff00000b1086901f6b0613811bb611d000000717a3402ac2908a505227094dc119160261f06d3000000000000000b07f62006d4024a700bc6076a104fdd07ab200f6a014640647a08f70000000000b08f000000c141e7043200000a070cc098a00000395d9d188f000004029e206b4d10d1004b7204694061250478d0931617ec8962200000000001012a000000000000000409450000000000d1900000001160ac13b7006a900000000000000000000f17c40000000000d02770000000000000000195450179b012700000b01f901293c00ad10114b01c4903b4703e3e04ff00 else (if i<4 then 0x20792c0343703177020cc0803d036dd08e4d06de000008038200000f048b1057f908a8a0329e08340134f201b271a02c0030409dd11a006026a80a21d04c11022e2096af07ceb0993192206022c11a2000000d06644026cf05f7b15da505d6a06cf7066ad0481909b4007e3407a6b03fc8039a81384e07d2e1028000009136b509f8a15b0d01c151211805f900000602d651755000008009c11811110df201b81080ed0777d0039904d33015d31783704f5402cf000004049410892901d000000d06e4907e2304e8c0313219d370077e04670054e50679c0933e032530073e0904608b53180d00000418cb40400214be00000e1531b9626902ff00000014fca14a5000000000000000c0130b1925618a520941f0a00c057300000a037410372200ee20488c052d304620000090854000009054d30477b165ab0526a05367049e0000000000e09f50000000000f193810248b06d9c04ea00000000008050e00328202fd00000b07eec016900000b0145f95e460033000003033db0960914b7b081ae00f5d04c65098f90793203d4a09e510898d12edf013b3033690641910c64075dc01120056a00000803c4c95f070506000000000050205201bce1230c025a912667120540616703c30000000000404bfc0102d0009e02a3709f40000000000818bfb0934402589068ed01485151bb01ded06b6207d95050f70032d07a380544b03da000009014d00516511d22186e101b9e0987c033e00000000001065a8008a509c100000c00f91051b118b0702a2706b000000000000000000000b03111025ea115700000904eb4006c000004016000000817bc2079b7034f0000000000e01aae1540607d611538618d700000800b800000005da9086fc0349d03f7e09e410618400b57099800000000009033cc01e600000e09fd00000308add015e0000000000905980175720569c073860715b1807f048e00000985cf3075b8081d516a6609d7f0511c087000000000350179dc092210651808fcd00b000000000007066c9082b80640214e700595603e500000000008072b212d20000000000000000000000000b04c25135bb01920009e00925c006f00000815b900000905f5c0377f06a0e05900049bc087ac197d00000c0876000000000000000000009018c00000000000000000000b09e7e045600000500ccf002580a1f706c8000000000000000000001061c00000d05cd00000205926099da02faf0115209b2a165071144609ea00000e14ac00000802983127df13f6404d410a207078a00000c120e335d781688804c7b0765db560506f5b19dd0090ea020e5052be0237f01265053a114b900000419ad60153807103067d60190e033fa060ca078ba14e0711972013f414cd00000e08a48083220955f0587d02ca20373906dd704046120f300568069 else 0x1300000f005cf0994519bb414aee0670b037e4046500000207d8907f58020aa0498000004193420828e0a2c208f10000040762f049d11a07403d33057b409fb00000409ca609c000000a0299c1973102b5b1719307b540212b01972098b6034a108202082400602d051d50874216d5113fe0000000000805d30000030240305fe900c100000409f0f0837c087300000d07d3b07aa0000000000e01178025d506fcf071f608eba02b370654f034b301bf4083af09e3d036011640200c3602ef6995ad04a4f16b5f117b40606f05c590029000000000000000109cdd1029b07f7790d44938a00000000000000000000008160000000000e02f0e0766000000000000000c072f2054fe07350000060272e10ea0000070861f0223501f2e004000000807eb000009077e000000000000000406b8311215014c604af000d2d13860000009623410640000000000206080000000000300eab15e910142c00e4c038ad0923b055000000b06af00415b033b00000201dcc0091e02fe30964d06b700000000004078470254f07b431604092e2408a9013ac00000c0065a010f9160dc03d02164900000007b7000002015c00000b050d201f8803ba3084a990e200000c08aaf08d2595fa30238b06bcd02b990742712fd00000708d461998513895007a00984701ead05d5e1277a03f1904466025c8004d109b0f11b5803e2201ace118b6181c10437006f1006d24051c000000000000000c181b000000000000000d08bae15f6602bd00000408360000041771000000000080845d14b4a1328e024c7045fb0a250000090985204999075400000d0048007b1310b7b111c08958e018e819814137800460910108139bf03e0c039340871e006ed16f7d05f01086221391500c5908bb000007024d602d8108380000030560102a41002411826501500000030806d097cc08e6c18bc000000000000000c00950000000000c19320000000000000001096f0000050943d0331000001023260831000004035c00000405dd0000000000c055ea04c500000000000000000000000002035200000e087db00c700269a040b615ef0000000000905396097300000a00d300000000008030bf0101000002001100000c058600000f0383000000000071234000000000000000a06b2f0134000005047000000c185bc044b9090d580e1d01a930656d0292709c5c07dc604179120cc0156000003058e300d5c052400000f00bb4052a91642d09d070381d02aef0847704ca00000101400000030436d151cf03560000060805a00c08074000000514b0509468050860584000004034ef19abe0255e062800000e0977009f901176c19d9300e951516f95f5003ae6130a00000105186106d1193cb08c6308d10000000000000008057e0043c0000030859f02f1b09bc916d47026e000000))) else (if i<8 then (if i<6 then 0x504015159d00000917966105fc0844e05c900000e06446152fb0974705c8d088200000000004095200000c130f2079a505e4000009062c91301302df00000209cc81799e02d5d091760347103799096eb01b0f04a11092da0376908975046a000004017e00000b017fa017300000c95c98020300000a01938011600000c01afe07041009ba03f8602028009f000005126f0000031063519c6d07a040045601e1e0970718a4413939062d1062361884609160000000000e046be11b6507b80000000000203fb1040e8192f9042c60972d00a3e00604953f400a1100150022d00000a01cf2002740680a0954d08fe00721c01ba60558a057990253e066e304d20000070367316bb000006160ec0a0e00000f155ea06ad00000e0965507cc00000000000000000a1eb00ddb0483d1537301e27007900000d0864a028ce05ae505fd702f90000020003002e340578002910000080564306c1f006310480209ad9181400000000007066fb01b100000c06f4000007096690358000000000000000a09409029a4022200000200340000000000313e450999806d7c05b7e15fb016aab070b8094e015c720111105652012d902e0516397059e919fac06c2408102076c0000000000502f2508d0407ae00000c091071350302baa0663b041b0000030992f0888000003038c0000000000200f4306ba0000061791908d6600bea0021407c5103f98088e00000118011175db061fd08e24123b202f40000000000e087b0000001928f860c907fce003ea15b1000000000000000000000097e00000e06bf606fbe159c4018b4030df08d7519122108f00996801a0e09ec6012bc02be10755c0855413f84060f50541008dd8094a2081e806c5709e0000005028261143c0419400b7f0548a05eb807a4b00fde0092706c0000004036f4058b00000806ceb01769055500000000005054b0000000000e1281805cf000009021f0000060981f1890806db8069b209d9604dd0000000000c0310503340000000000509c400000f0774101a28106c00000718ef8054a20107904c90000000000b16bd505d170547d073091141c19f3b00e8000005083f00000301728160b1069aa0600401c81074b000000000000000d0856b08d361235d0454c091b813751063b217c300000202356027ec05d70000071881b02d2408e5808124042b00000905830000000546d001d3028df04b3b0729105c1f03ef80553918f200000c0687c11d4e17ef000006026850072b102d000000000000000809ee417eea05fa5091c8074fd062940338e03eda0259000000000000a06815d5a093f615a8500b2a090f907fe2037d403d700000005c6500a010552a11b9912d0a0700000000000000000101cd000000000020886807e41098051318e08bdb35d4008330139c60a0bb04d190076701da602 else (if i<7 then 0x7f1e08ed000000099ac03970000000000c087cf08c2a065fb94eb194cee00a74096d00000504d0f12dbf01bb6073c00000c12b750842a001e5105e01408f004700000403420083ee0a0a00000339590000030420a186c608f8a07f49131550361701d8f07110000000000c07611042d1086d800f75088bd0341000001005e7950db04a0710a80000000000f074ae03eea067bf007c0000000000c119680070d9287b0a0db12fc005b940709703ec408c4000009089a000001028e00000609da0053d00000b0575610e800000700680000000000311d1004fc000000000081990807ec90276100e0307673010e0000000000f05de00000d0643b021500000b1296104f20056d8107fb02ddf02666063f909c71079e90141d15d40000081902e03a8106a3000005055d309532098cd043f805b44096800000b195700000606df5073d0000030100114a400000305319043400000a04f3f03c7000004078500000213e8f0a2ac04e40015100000207c6a00c2b06e6a09a6707be804bd8062650875a0789a1862c09b75023600000e15810000000000403f200000203ce00000e03e8001b7507908089600000b01cbf011de04180000080323000006038d000000000000000000000000000000891890000000000406fa000008011c1068f00000716ad0000000000000000000010513605a9b09c6b0a11f078f5016a7046f0000000000596245085d2076ff18b10000041311b0132a030af0849909af8022aa04e5f0a1490661a0930e04da808cef165ef12700087f5090bb0986405ba50387d1769cb0b700000800e50000010106d09e94027500000406ab00000d013af192c00000d010b000007153580023608eec039b609a30032d618fe00000513ffd08b170912f075e4112e41985f05b8b1210e0389f013d400ce001d1a013111188e0911d1274404fbcb55e1084f20472003f0a038b00900609bb7024e00000f02d9102292019e00000d01379032cb06cd708c0304cb8052141195117eba08f46003c70637a18dc00000b0008025cf59072408e1004f6017720000051588001d5815c5304e6503f30000000000603d5208cfd0399115cea017cd003d8158500000000005161c00000904b19013e30424509f3d05a0795d790210319e92010360857919e8c04921088fa111f00000300530000000000603b9107f8108e3904f7f01dbb08487020d1106921358306a80059ff19a230530f094940551718f0400947078d70a08304b2b058d303cfa002c917e9606ea700ff00649400190000000000c05ac9037a21898c002a509c800000d019bb0685b14ca301ef51794b12eaf04021081110682f09370008c00000092fe501be0114c310d8000000000050990706750000000000d0948f0769f00d70000000000f01d650746f04a300000000000000000000 else 0x1f04076a57b5136191a0c0000090260e12e0d05e3309ac00000a030c00000103ebf01684022600000f1a0bb180ab053c8023a000009008100000000002081cd121320683000000000061080816063058a00000d18f600000314a3614c46184ea020b000004060400000e05b0702cbd06522092400000a064f0000000000c09d6815b8601a62063671171211d9c12406027920080d151ab08080000010486908dc112f9b0914d017b405280000000000a04ade019c30650a0170201755049100000b1824e195bf0452f052c0000020113000007127ed09970000000444808800000000412b01fa80743602c97090300000000000056cb14a8217b8804138022f700f28059a1031d7078320901e03dc305f23017161239508fd304d500000308c7a02de9046cd05cb9045b00000304aa0050a00000601ecc05f40118f000001085000000708fbb009aa02979143270696f09f6506b5605cc802909080f703dd818b210416701890000000000c04a200000804ba326079051aa0013c1659f0658d03b8b01632057ae02247061ec1964c04d6d056f517fd4085ee148ec0221b004400657006762080ba04c0207498147be081980442c060bf166ca06bd00000918e7605e7a4587c067f70218a13fcf0209001caa0020414ba7011e1058fd0594506309072e606edc19ae806e0f0211801fe806a1302daf01fd9024b009b800750c071ce06d650788700aca08cb5029420042904b6a07f01034ca00fbd02072084df0a029019ff176df0490a0200806f0a134b90a03000000942bf08fa003a7300daf040d10a1200000a09757009870509d062ba036e408b9512b080369d15397075cf03cd7041f0068d908c8c072ab0589f00f0203375004f506a26066bd09a95074ce9959e082d308f6885da709ed00000110bc008a2e00ab00000a1806a0631d01e75026f009e1e092b40466101473119d706c9908db900cd0000000000b052f2049c1000e102f8a03219068a708d8300c6b011f000000086671511d1360b080df08ef00000b07df8130e6035bf082900000707e1406e5b071d404519058500000c00ef000000000090716302b63106200000906a4e067c30514000eca15de00519903bee013671698113e32067a00000501c2403af4090a00000407de0000000000e11c3a043d5062ad03ad700e6e196dd0450c1565710eb00000b14bf40157a00c400000408c170753e09b3907fda015800000000fa80804d14c9f04ef007bf9041a0000020403d01c600000508a1e01d710561e0326000000083da079d804f0907e800000514c2e09fcd1661e0863906d4903bf2049fe026b00000f07c3b0918e0214709dc517972006650165118baf03a1a03fd402d00000090574c15aa00000601c700000d0365000000021b405a500000007e0c17dc0000090633306dc91)) else (if i<9 then 0x15a650697c023b8072300000d03cc00000d195500000207b0d02cc4074d20375000000000041a01718be1044a0000000000000002016600000419dc000005032b708e9e01d31117350731704bc30689508401099f00000f13326089d006e85151d902f3f16b0913e0e03544019800000e09c33154d205a310a2b00000f069cd095cd128d801a37557b0000070319102730000000000a14a7a080c918611051fa00de50395000003110c0000070124a09a0b09a800000703a6b0958b09b52001a8069d0000000000d1199603350000020241b05a4492b600000000008103400000f08ec91355c04b0604a7f00e330887e0046607c890406a0274000000000000000507820000000000001e8000008010a207ad00484000008073ae05e5b11130000000000c055c307c0409d2c185f307c900000d04cdc15ab0000030028a05ee5183400000a045dd01a71031ac088d0000000000f086c00000b01ed502460000000000f06ccd01c9e03d17093d00000b0a04307390000040813e04ccb023c10823901c00000000000405bc00000003bd00440305ec119fd705ca60611e199ee10b500000f960200000719fc0000020725712af0000020927f072230307b06ff3002de13f53045e00000000000000000000801dda036800000f0959007b95053f60464a01a880533c18d9d15a161349200b3417be00000205fc000004049ad0728815fee0540d094f6086a00000708b3015c80000051214a003a00000908b401097d14af00000c018f4039c2118d506986042661030a109190801f04630083000000d0772317f400051709df607d1b05fb403d22067700000a00cb00000519af000008055f916717065520a131065c0000030026200362046d000000000000000b1820000000063dc0105f0428c009710744315e4b06ece05e900000a18968027020485c036ae09ef9082f00000e19c900000b02fc00000000000000000906005c43026d601224124950411911bcf1104a096b300373044eb015511291103a080a26c05969084c40061702e9e09fe013e7000004076ba956a10120e000110075410d0207594086000000a07e5c03e7704b4108390000010370200ba403c65008460752104ce30a079056880877b0293104532002e00000195e6000009047f00000305727099c212df90449617d600000d04b500000000007017dc044ff06d12057c002e6502e2b0763c04fe011d500000f95df3093a00000c120bf051e206e3d07b6405ffd07145115be0371e06279043a105bbb0314000000000000219e06660099b800f1705036019d5066991729017e290194306cbb07dda0591f091ff0778635e6004bed0109d06013190f00000000001007df0181b03c5608bc0000000000a120a00000a15a000000e016fb057dd0082d12fbc95d88118200000906780047 else (if i<10 then 0x560000000000c05572196f00000718ed6028900000211270000080149000000000000000504ec000009079410780510d9214edc09710000000000b07fb00000605d90000071828e04edd04d7e082c00000000000000000835d0868b05e0700fec03ea0000091838816823024f403fa218cd101bd803dea004331377a035a40a1c000000085a00000000001073e8014b515704074500000007a2c0459e1664c0445c01192085b000007078740867407917079c20956d082a0000000858e06d801899407810000000000f15d6000001091d00000c0250b0671000000000000000e097fc01eb900d6d05a8e00bf00000007d0000005045a20295702782004b8066590064c033af00e131002c03a9308a6f0852e021a3067300448a0267b102e0000000000400a6a0768802ee214b2d043b608e000000a08b0f02d300000000008192d705078048d507477175fd17d400000b0164d03f400517401f7801b63050b206bb20799f02bf106e9c085c6099150775d02fba071b91236c19f8e0881000006041c300d1e09a710366903b2a004c000008120600000f03e9b01807025f3018ac090ca0736016d36031c31877c90e7e05b100457205ce10093513667014a812c4d1090507fa501ffd05620029f3021c90090403915000f4097da01ced17bd0025b900382092f81309008a090069704102030e8087800000306f9606c7903225007bd041dd008eb047a307af00000a060900000912a1c095ea039d8092ec00065092a8095a300747052980929c02d7509eb603c9304a5a027c505af109bfc0773313fae02b0302dc60129b0532108dab000b1038050245b0050f06172176eb19ea900591049340713d089e6084ea047c906ee00688800b4f06746073760818b10c48052700000e159e6020610879f063910702a02e5f0719a1776908aec095f2028a00242818ccd10ac40405c00aa903a2d05669020f206b16088af1335203a300000900aff18ebb01f07045c302c1700a24062f000005063c809f280648503db4093870534b02e7000004050ce167b61586b13f3903857179f500a50000000000801f36032a90890f188e505c0d0327000f300000000000102ad02c8100c9214049064c9019ad0088a03842055b006b92035ed02bb6088cb0703a00316199d5001c000000000001778814b850786204ae600b18059c201fc2019900000501abb15e36008600000e05a7609a1708b73039e4015a10899c11b2e05d220177000009013911647a05bd2070590249803153102cb09b141777000000016d0000020152c02c0c0234e00ca402a90000000000f0154501df30620b0178d099591149507cb50827107e700000104293907331993707bdf09a2b0779f0891c06c6d02a88083c709f1507bb5041e117a0305a1307f1c060a9016ea054ca0822b06d0a18fce else 0x414f7f0672c0225704f93070e002af000000000000000104a9000dca014ed0908000007049620667911b8208b2b0256702870011ba09db000001022800000907f3601824036ba093cd03a56032ea09880031e903abe07d4215648098dc00df8113d1005d508f96002ff01cc8003f004fa41579d011a00000b03cad06f7204bb30320808cc0000090976b0220e0052000004084600000c05b34086570615f003b9073b318034023de01a44047590902605aa0128660621d0474b18ea0095d01906a0545805015079810441a1989a00ebc07ea30712a0012e02ead0825b0625b006230a162021d807cf5038fc05238175a601e570262d0280b16d1713ae10071010be315a5b072400000706e2e01e96034da1628a066dd065ea035df0138d141fd059900000e07483129da05e100000000008005be065390306d037c00000e0699a09d500000c09ffa01aed004a501eec04f4807326043970614400e7b07ffd17ff1084b800c860067c0915d112ca109ed0758000000075fe05a6516f8609b6700e200000107e9a15174188b000009078e108c9c09aee0821e176f803e4f064e506dad0392907ca4093e401d400605c115e708d9f0049f13953035f000004068b111cf50187a13140000040869b059bf19f63015fd03c160476f0332e174dd1868e0843d092c8064de05591054280408610c7c07266042f502f780807c01959073320638605bf2000c01971502f560635205493193340a242046ec0951e01880000030a17f008700000706aa00000000000000000000713ea211d3e04330126e80907600a410751a15464046100000a027b51515f09de800960000000000315837115640495f03d9000002056700000218ddd097b4008b607a980505b070180089915e5f15134012fb140ed1a23504795133ad120db09fab80ea8037f000007062e00000000004098e709c2a0571106a5305703059d00000d059701641000007088900853806f810525000000000040284706950063aa05ada07db405dbe08ded179210515a0694309573027a701b3000003001fc085f000001137e0000061066805e8704b96073fb11b300000000143016c802a6e058c809d1a0926d07181008db029da0264904ac307da00000c0942807414123c814c100000d0286d0351709e600438904ee000000094400000107083029c0000080a2790288b08836077fd09e820121912e500000000000295800000102a770928704099010c00000909b900000003e1417d130303302650000000000212ce000000000081790000008070af02eba07ef807c7a077d40983306b3a0227f02010000040884a1995a00b900000d08e7403508077a00000207))))
def hashcombl13 (i : Nat) : Nat := 0x3c41c01bfc29900a000010164000000000000000000024094000044e542580000000242140003c42800008044013781240003418880d0000342c186980003400800000000000000000000000000000003819d026e8104000000000000000282640000000000018180c2280003024fc1aa430740e80000000282500000000000000003c49400f4000081380000c230000282a0000000000000000302880000c048000085c40003861ac1280003c148c13e419101ce82768184000000000002415c0003c20101d9003c00000000000302680000000000000002c02000000002c1300002c29cc6030651047d817002400161409b42040077021d004cc0e14287c6e340ec0000000141f2c0244608000000000001010f80d68679001142d400000003c0308294000342ba40280000000280b7830c00000001c2ec000000000000000204d3415000000000c06c0000000242fc817ac50c00020248000000000000000206380002c09240c800000001c2398577c0c00000000000000003c0ae825e822682f6005c40aa81ef81ca000f023c0002028c000381e802180000000342ce42440003c11782e28689c007411a006400000002c26386240002c21000000000000000000000000040fc40c6c2e4000000000003062800010314000201e7c6ec0003c0dc0000427c0000068400000000000002540000011044ac0001827042d9402ec034000246d400014083063500cc000105a280f80001031a866286be414cc2f0816c0003409c0000822d0177c4e2c2aa81974521c1080000000000004612c550c1d00003430341fc408c801f02fb01aca5840000000000000000000000000000000381c340a40000000381f6c567447b01e302af0078000242c800000003c016c4380000000000000003c0b80003c1b400000003c054c121c1dc8069829282de8140407d4147410000000000818c000000000000000000000003808482bc0002c2e800bc0000c1a0c4540000000000030283c4fd022080e4000340580000000000000003c2b0445c0308000000038702420905ac000001a6c0d980f140b142d144f982c542b401b80002c311c2a5819b4070017e411f41d40000000000004477c711c06000038595c156420f408bc4be01b3c5838018000246140000012c0000063e40380003c27801f800030234805000028169c15b4715804041c4000202388000844011c8260584604c01144501c0038480188421080013102320680144c1886103882
def combd8 (i : Nat) : Nat := 0x2f3254e2a5515498160a00
def combl8 : Packing := (1,7,8,0,0,3,0,combd8)
def combd9 (i : Nat) : Nat := (if i<1 then 0x5006ed8571522858160a00bdb056aa2a9302c1401e36551549812a582803d6c152a8aa4c0b050066dc544bc5958160a00c6f88e2f855a62c14018df17b470a3285828031be2f68e15250b0500637c5f11b06ca960a00fd312aac2c0ac4c1401bdc2115f03b609328031be422be15698b050071e98462252ca960a00c6f908af95db4a994017b62dd54552605828037f0302a605698a650057e25342c4ec514ca00c5dca631855a62c1401bf82115302b4c5328039f44231129654b050067e2aed4c0ad314ca00fd31332a2a9302c1401bdc2774703b60932803f70488c0a62c1265006ee29118c0ad314ca00c73d2a978d0cccc1401bbc11d6302b4c532803778318c085698a65006ef063182285314ca00bde096916c0a6299401bbc11c4c4a86093280377827898856c0b05005ef04b43b4c58160a00dde09e26450b02c1401bbc18d4703b60932803778238c0876c1265006ef061d1c0ed824ca00dde05e30298b0499401dbc0bc6053160932802f7825a4c30298a650057f04743c4ac984ca00bde09692698b02c14014fd13d2951b28d82802bad2ba162f650b050053bc5b4a546ca360a00dde0a0b1815a6299401d9c8bd609875cd32802b7931a1627628a650056f26342c4ec914ca00dce4c0af81db04994013dc97d2f13160932802bb927a162f650b050057725f43c4ac984ca0087ecded98d1946c14010bf9bdb31a82a1328021ef37b6634a52a650043fc6f6cc684a160a0087f8ded98d094299401bbc2116302b4c5328037694aac605698a65006f529557c0ed824ca00dce5442f81db049940189fa885f0ab4c5828038e6cab08a9654b0500627ea217caeda54ca00c775112d95db42c1401cf32558454b2a582803f58466b0b02b13050063768cd7c2ad3160a00e3972ac44a5952c14018eda335b2bb685828031bb466be576d2a65004ff0b751c0ed824ca00dde16630298b04994019bcabb6302b4c532803d78554c0a62c1265006ef0a211c0ed824ca00ddc54429815a6299401cbaa888894b2a5828039e54ab1129654b05005e72b758261d734ca00cee55daf81db0499401e9caaa609875cd32803f584ccc0a62c1265006fb09991c0ed824ca00dd653331815a62994018dda332f1a59dd328031dd4445e3433330500627ea20bc696774ca00c76d19978d0cccc14013dcadd5f03b609328024fe13aae34f08b05006bf0aa91c0ed824ca00d6e5552f81db0499401abcaaa6302b4c5328035f1554a605698a65004ef2b758c0ad314ca00ede15db0298b04994019fc2bb4703b6093280376c598a8aa4c0b05005ef0b75814c5824ca00f5b1552a2a9302c1401eae2aa58581589828023bd19aa92f650b05007e581f1515498160a00fd6036b0298b0499401c9e987608ab5c53280333d30e5e2e2b13050053765f4a10eda460a00 else 0x1a0e68488078204f023c044e8384f010ba021000d810420e1841c20000000001f0007a060f40c100000000000000000000000000001f0007e000fc001000604080003a81000360de06083e000fc0010000000000003e000800000000000000000000000002e06080605083e0004345f00040000000f80010d10000000000000000000000000000000000000000000000000000000000000000f8003f0007e000fc010838be00841c5f00069a52fa393ee744d59852f6554a59251fe3d4758e11ae334618b915e2243183d0660a40f815016003fb7ecfc5f63e77c4f75ec3d379cf25e23bf774ed5d83ab730e15b936d6d0d55a834b638c25822f15bcb656a2cf594b15602bb56cac556299528a3d452855009ed3b2714d899d3125d4b094d272494888fd1d2354608750c20540077ce61c73846f4dc1b335c634c41832fc5e4ba16f2d4594b015b2ac544a61472844f49c13325c4a49211f2344548810b20c4047e0f71e43b4740e31bc3646a0cf194314600bb16c2c4560a71442744c09311c1ec3405506804c0074eb5498152ca960a00e9daa8b02a5952c1401c7b5516054b2a5828028f7abad0a9654b050064ef6054c26e3360a00a3deaeb02a5952c140187bda15309b8cd82803e6c952a8aa4c0b050078f94c552604a960a008ef666aa4bd942c1401c9ed87608ab5c53280333db0e5e2e2b1305007ed0955814c5824ca00fda119aa2a9302c1401c4be779994b2a5828039974ef3329654b05007e2a911875d96260a00fd91222a2a9302c1401faa24458581589828037d14cca605698a6500636e5317c2ad3160a00a6dcbe942a5952c14014db97d06d4b2a5828039d64cd08a9654b05007e629118261d734ca00e35b33422a5952c14018dba445f0ab4c5828031b7488be576d2a650063ae910bc6866660a00c6dd22178d2cee99401f9c2776053160932803f1c4eeb0b02b1305007e708458261d734ca00e6d93bc22a5952c1401f8ca3361d7658982803d1d554c3aecb1305007e329998261d734ca00de65332f81db0499401c5b6778454b2a58280319f4ccbe15698b050073aa99a2252ca960a00c67d3bad95db42c14018cfa662f1a59dd3280319f4ee5e3433330500633e9997caeda54ca00c75d222d95db42c14014db97d2854b28d82802f6c27aa8aa4c0b05007ad854552605a060a00bdb0968b6a8b02c1401bb615c5442b60582802f6c25a4aaa2c0b)
def combl9 : Packing := (161,6,8,1,4,11,0,combd9)
def combd10 (i : Nat) : Nat := (if i<15 then (if i<7 then (if i<3 then (if i<1 then 0xcff11b06da84ca00cbf98b22da04ca00cff11b06da54ca00fbc9312a1824ca00fbe2112a1824ca00ebf2116a0a84ca00dbeabb2a1824ca00abfacc6a0a84ca00ffc182285314ca00ff5255285314ca00ef7255684a14ca00fbd288285314ca00ebf288684a14ca00dfd2bb285314ca00aff2cc684a14ca00cf795b16da04ca00cf795b16da160a00fbb2442858160a00efb244684a160a00fbd08b605314ca00fbe1322858160a00fbe1522858160a00aff11c28ca160a00fb72552858160a00ef7255684a160a00ebf288684a160a00dbf2bb2858160a00fbd2332858160a00efd233684a160a00fbe2222858160a00efe222684a160a00ebf2aa2858160a00aff2cc684a160a00f9f2772858160a00edf277684a160a00aff11c2a4a160a00cfb8a152ca360a00cfb8a152ca960a00cff0a546ca360a00cef8a55aca360a00cfd8a10eda460a00dfc82c4ec514ca00fbaa440ad8160a00fbd03b4c58160a00fbe1310ad8160a00fbe1510ad8160a00dbe93b0ad8160a00ebeaaa0ad8160a00fb6a550ad8160a00fb705b5458160a00fbca330ad8160a00daf85b1ad8160a00dfc82c4ec914ca00dfc83c4ac984ca00dde82c5eca160a00cf795b16da14ca00ee7a66694a54ca00af7acc694a54ca00ef7211694a54ca00eb7a88694a54ca00c7bc5152ca960a00cfb85152ca960a00fbd0934c58160a00efd0934c5a160a00cfd8932ad3160a00fbe13222e1160a00fbe15222e1160a00ebf08c845a060a00fbe22222e1160a00ebf2aa22e1160a00e3f48c844a960a00ebf0a922e1160a00fbb24422e1160a00f9f27722e1160a00fbd01b4c6884ca00fb725522e1160a00fbd23322e1160a00cfd8934eeaa60a00cfd93b0eca960a00fbd098605314ca00fbc9310ae884ca00ebe9a50ae884ca00ffc1820ee114ca00efd03c845a04ca00ff52550ee114ca00efd0a90ee114ca00ff605b54a1160a00fbca330ae884ca00ffc2220ee114ca00ebeaaa0ae884ca00efd2aa0ee114ca00fbaa440ae884ca00fdd2770ee114ca00fbd01b6063360a00efd01b6863360a00fbe2110ae884ca00fbd2880ee114ca00fb70955458160a00fbc9810ae3360a00fbca880ae3360a00efcaaa0ae3360a00ff4a550ae3360a00ffc2110ae3360a00feca660ae3360a00cff11b06ca960a00cfb81b52ca960a00cff11b06eaa60a00cfd93b0eeaa60a00c6be6652ca960a00ceba6652ca960a00f8e9875d96260a00fb61515498160a00bf894c0ad314ca00fbc1814c5824ca00bfc11c0ed824ca00fae1616056260a00f9c98261d734ca00bbc98c0ad314ca00bdc97c0ed824ca008df97c2ad3160a00c7b61152ca960a00c7ae2252ca960a008ef96caeda160a008df97caeda54ca00cfb21152ca960a00cfaa2252ca960a008df8bc696774ca008ef8bc6866660a00 else (if i<2 then 0xcbf9872ad6360a00cf7a552ad6360a00cff2112ad6360a00cfea222ad6360a00cdfa772ad6360a00cdf87c62da54ca00cdf87c56da04ca00cef86c56da160a00eeea221ada160a00cef86c46da060a00cdf87c46da54ca00edda331eda54ca009bf8bc5958160a00ecfa771ada160a00edba441eda54ca00eef1311ada160a00cef94b1ada160a00cef93b1ada160a00cef95b1ada160a00cef90b1ada160a00cef97b1ada160a00c6fc9b1ada160a00cef89b1ada160a00ede9821eda54ca00cdf96b1eda54ca00cdf98b1eda54ca00cdf90b1eda54ca00cdf91b1eda54ca00cdf94b1eda54ca00edf2111eda54ca00c5fc9b1eda54ca00cdf89b1eda54ca00eeda331ada160a00e9fa881eda54ca00eeba441ada160a00ecfa661eda54ca00cefabb1ada160a00cdfabb1eda54ca00fa7a551ad8160a00fed06c605314ca00fae9321ad8160a00fae9521ad8160a00faf1311ad8160a00faf1511ad8160a00eaf86c605a060a00daf90b1ad8160a00daf93b1ad8160a00daf97b1ad8160a00cef9ab1ad814ca00fada331ad8160a00faea221ad8160a00daf89b1ad8160a00e2fc6c604a960a00eaf8a91ad8160a00f8fa771ad8160a00faba441ad8160a00dafabb1ad8160a00eafaaa1ad8160a00bee8ac5956260a00cdf9a72ad7160a00cdf9702ad7160a00cdf9872ad7160a00cfda332ad7160a00cbfa882ad7160a00cf7a552ad7160a00cfba442ad7160a00cdf9702ad714ca00cdf9872ad714ca00cfd9312ad844ca00cff2112ad844ca00cfe9822ad714ca00cbfa882ad714ca00cf7a552ad714ca009fe8bc5c56260a00cff2112ad874ca00cfb9a42ad4160a00cff2112ad654ca00d5dd7326d874ca00bdd89c61d734ca00aff01c5ada060a00cfd93b0eda060a00ebf01b605a060a00cff11b06da060a00afd83c52da160a00abf88c5ada54ca00aff01c5ada04ca00efd03b4c5a160a00cfd93b0eda160a00ebe88b609a54ca00cbf98b22da54ca00efd01b4c5a04ca00cff11b06da04ca00df99410eda460a00dfc9620eda460a00dbd9810eda460a00cfd9a10eda460a00cfd9a60eda460a00dfd2110eda460a00deda660eda460a00dfca220eda460a00cfdaaa0eda460a00fbc9870ed824ca00fbc9810ed824ca00cfd93b28da060a00cfd93b28ca160a00afd93c2a4a360a00afd89c68ca360a00ffc1810ad314ca00ffc1410ad314ca00fbca880ad314ca00ffc2110ed824ca00ff4a550ad314ca00efd21168ca360a00ff8a440ad314ca00fdca770ed824ca00feca660ed824ca00eeda6668ca360a00feca660ad314ca00ffc2110ad314ca00fbca880ed824ca00efca2268ca360a00efcaaa0ed824ca00efcaaa0ad314ca00dfcabb0ed824ca00dfcabb0ad314ca00afdacc68ca360a00cdf8a35eca160a00cbf98b22da14ca00 else 0xefe21188aaa60a00ef6a5588aaa60a00afeacc4caaa60a00cfdaaaaed314ca00abfacc606aa60a008ffacc6ac9360a008ffacc6ac3160a00cfe92caeda84ca008ffacc6ad824ca00cff11caeda14ca00cfd93caeda14ca008ffacc6ad214ca00cbfa88aeda14ca00cf7a55aeda14ca00cfba44aeda14ca00cefa66aeda84ca00cefa66aeda14ca00cff211aeda14ca00cfea22aeda84ca00cfda33aeda14ca00cdfa77aeda660a00abf89c2ae884ca008ffacc6ac9160a008ff8bc4c6aa60a008ff8acaed3160a008ffacc6ac5160a0087fc9c5eeaa4ca008ff89c5eeaa4ca00c7bd4c26eaa4ca00cef96caeda160a00cdf97caeda54ca00cfb94c26eaa4ca00cefa66aeda160a00cdfa77aeda54ca0087fc9c5aeaa60a008ff89c5aeaa60a0087fd1c26eaa60a008ff93c26eaa60a008ff91c26eaa60a0087fc9c4eeaa60a008ff89c4eeaa60a0087fc9c46eaa60a008ff89c46eaa60a00c7f93026eaa60a00c7f90c26eaa60a00c7f61126eaa60a00c6fe6626eaa60a00cbf98126eaa60a00cfe92c26eaa60a00c7ee2226eaa60a00cff21126eaa60a00cfda3326eaa60a00cfea2226eaa60a00cefa6626eaa60a00a7facc42ca960a0087fc9c5aeaa4ca008ff89c5aeaa4ca0087fd1c26eaa4ca008ff98caeda54ca008ff93caeda160a008ff91c26eaa4ca0087fc9c46eaa4ca008ff89c46eaa4ca00c7dd3c26eaa4ca00c7dd3126eaa4ca00cfe92caeda54ca00cfe982aeda54ca00cfd93caeda54ca00cfd973aeda54ca00cf795caeda54ca00c77e5526eaa4ca00cff11caeda160a00cff131aeda160a00cfe92caeda160a00cfe962aeda160a00cbf98caeda160a00c3fe8826eaa4ca00cf7a55aeda160a00c7de3326eaa4ca00cfea22aeda54ca00cff211aeda160a00c7ee2226eaa4ca00cfda33aeda54ca00cfea22aeda160a00c5fe7726eaa4ca00cfba44aeda54ca00cdfa77aeda160a00cfd93c26eaa4ca00cfd93126eaa4ca00cf7a5526eaa4ca00cbfa8826eaa4ca00cfda3326eaa4ca00cfea2226eaa4ca00cdfa7726eaa4ca0087fc9caeda14ca008ffacc62da54ca008ff89caeda14ca0087fc9caeda54ca008ffacc56da160a008ff89caeda54ca0087fc9caeda160a008ffacc46da54ca008ff89caeda160a008ff89caeda84ca009fe93caed6260a00dbe987aed6260a00dbe983aed6260a00dfc982aed734ca00df6a55aed6260a00dfd211aed734ca00cf7a55aeda64ca00cfea22aeda64ca00cfda33aeda64ca00cff211aeda74ca008ff93caeda660a00cf7a55aeda660a00c7bd7652ca960a00cfb97652ca960a00c7bd6152ca960a00cfb96152ca960a00c7bd8752ca960a00c7bd7152ca960a00cfb96252ca960a00cfb97152ca960a00bee8ac58d6260a00cef9a62ad6360a00cef9622ad6360a00cef9602ad6360a00)) else (if i<5 then (if i<4 then 0x8ff95caeda660a00cfda33aeda660a00cfba44aeda660a008ff8acaed5160a008ffacc6ac514ca008ff98caeda14ca008ff91caeda84ca00cfe92caeda14ca00cfea22aeda14ca00cfd93caeda84ca00cfda33aeda84ca00cdfa77aeda14ca00cfba44aeda84ca009feacc4ac854ca009ff2cc46ca360a008ffacc6ac854ca009bf93caed8160a00c7f9a026e3360a00db7a55aed8160a00bfd2cc605314ca00dbe932aed8160a00dbe952aed8160a00dbf131aed8160a00dbf161aed8160a00dbf151aed8160a00abfacc605a060a009fe8bc9562260a00dbda33aed8160a00dbea22aed8160a00a3fecc604a960a00cbf8a9aed8160a00d9fa77aed8160a00dbba44aed8160a00e7d89c8cda060a00dbf211aed8160a00c7dcab26e3360a00cfd89b2ae3360a00cefa66aeda54ca008ff89c2ae3360a00afd89c2ae3360a0087fd8c26eaa4ca008ff98c26eaa4ca008ff91caeda54ca0087fc9c62eaa4ca008ff89c62eaa4ca0087fecc46ca960a00cbfa88aeda54ca0087fd5c26eaa4ca008ff95caeda160a008ff95c26eaa4ca0087fecc56ca94ca008ff89c56eaa4ca00c7f61126eaa4ca00cfda33aeda160a00c6fe6626eaa4ca00cfba44aeda160a00cff21126eaa4ca00cefa6626eaa4ca00cff17b846aa60a00cef97b99aaa60a008ff93caeda84ca008ff92caeda14ca00cff13b846aa60a00cef93b99aaa60a00cfe93b88aaa60a008ff9bc0c6aa60a008ff9bc24eaa60a00a7ed2c26eaa60a00ebf151606aa60a00ebf11b606aa60a00ebf161606aa60a00ebf131606aa60a00cff2aa46ca360a00ebe952606aa60a00ebe98758aaa60a00ebe962606aa60a00ebe9874caaa60a00ebe9814caaa60a00ebe9834caaa60a00eee96558aaa60a00cdfaaa5eca160a00eee96158aaa60a00eee96b58aaa60a00eee97658aaa60a00eee96358aaa60a00cefaaa5aca360a00abf97c606aa60a00afe96c4caaa60a00afe95c4caaa60a00cfeaaa4ac5160a00cbfaaa62c9160a00abf98c06eaa60a00afe92c06eaa60a00afe92c26eaa60a009fe8bca22224ca00cbfaaa62c3160a00cfeaaa4ac3160a00cfeaaa4ac9360a00afe92c0eeaa60a00bbf2cc4c58160a00aff2cc4c5a160a00dfd181aed314ca00dfd141aed314ca00dfd121aed314ca00cfd9a6aed314ca00afdacc4c5a04ca009fd8bc846334ca00dbda88aed314ca00efe152846aa60a00efe162846aa60a00efe132846aa60a00ebf187846aa60a00ebf211606aa60a00ebf183846aa60a00ef7255846aa60a00cfd8a9aed314ca00df9a44aed314ca00eaf98199aaa60a00eaf98799aaa60a00eaf98399aaa60a00eee95299aaa60a00eee93299aaa60a00eef21199aaa60a00deda66aed314ca00ee7a5599aaa60a00dfd211aed314ca00ebe98188aaa60a00ebe98388aaa60a00 else 0xcff2112ae3360a00cefa662ae3360a00efca222ae3360a00efd2112ae3360a00eeda662ae3360a009fdacc4ec854ca009feacc4ac5160a009bfacc62c3160a009feacc4ac814ca009fdacc4ec814ca00cf796b956aa4ca00cbf97ba22aa4ca00cff18b846aa4ca00cbf91ba22aa4ca00cf791b956aa4ca00a7bd4c26eaa4ca00a7dd3c26eaa4ca00efd1214c6aa4ca00efd1414c6aa4ca00efd1814c6aa4ca00cff2aa46c854ca00eddaaa5cd704ca00edd9875ceaa4ca00cdfaaa5ec854ca00cdfaaa5ec814ca00adf97c22eaa4ca00efe21150aaa4ca00efe21160aaa4ca00efd2115ceaa4ca00efd2114c6aa4ca00efe21188aaa4ca00cfdaaa4ec854ca00afd93c16eaa4ca00afd93c22eaa4ca00afd93c26eaa4ca00afd97c4c6aa4ca00efc97360aaa4ca00efc93150aaa4ca00efc93160aaa4ca00cfdaaa4ec514ca00cfdaaa4ec814ca00cfdaaa4ec914ca00afd93c06eaa4ca00ebe98360aaa4ca00ebe98760aaa4ca00ebe98160aaa4ca00cfbaaa52c854ca00cfbaaa52c984ca00afb94c16eaa4ca00afb94c26eaa4ca00cfbaaa52c814ca00afb94c06eaa4ca009fe8bc8ce2260a00cfeaaa4ac854ca00afe92c16eaa4ca00afe92c22eaa4ca00cfeaaa4ac984ca00cfeaaa4ac814ca00afe92c06eaa4ca00ebd973a22aa4ca00ebd931a22aa4ca00ebe942a22aa4ca00ebea8860aaa4ca00ebda888ceaa4ca00ef6942956aa4ca00ef5931956aa4ca00ef7211956aa4ca00ede9829deaa4ca00edd9319deaa4ca00edf2119deaa4ca00ef9931912aa4ca00efa982912aa4ca00ebba88912aa4ca00ef3a55912aa4ca00efc9828ceaa4ca00efd2118ceaa4ca00efc93188aaa4ca00ebea8888aaa4ca00ef6a5588aaa4ca008ffacc6ac814ca00cbfa88aeda74ca00cdfa77aeda64ca00cfba44aeda64ca00cf78bc954a94ca008ffacc6ac984ca00cff0bc844a94ca008ffacc6ac914ca008ffacc6ac954ca008ff89c2ae1160a00c7f4bc844a960a00aff09c2ae1160a009ff2cc46c854ca009fdacc4ec514ca00cfda335aeaa60a00cfba445aeaa60a008ff92caeda54ca00cfe91b58aaa60a008ff91caeda160a00cfd91b8ceaa60a00cfe95b88aaa60a00cff15b846aa60a00cfb91b912aa60a00cfe91b88aaa60a008ff9bc146aa60a008ff9bc246aa60a00bbf2cc5458160a00dfc92caed314ca00dfc942aed314ca00dfc982aed314ca00dfca22aed314ca00efc93b4caaa60a00efc9734caaa60a00efc9314caaa60a00cfbaaa52ca360a00cfbaaa52ca960a00cfbaaa52ca160a00ebda33606aa60a00efca334caaa60a00efca3358aaa60a00efd233846aa60a00ddda77aed314ca00ebba44606aa60a00efaa444caaa60a00efaa4458aaa60a00ef9a33912aa60a00efb244846aa60a00efca3388aaa60a00efaa4488aaa60a00) else (if i<6 then 0xcbf97ba20a94ca00cef97b998a94ca008ff95c26da74ca0087fc9c5eda54ca008ff89c5eda54ca00cff21126da74ca00cbfa8826da74ca00cefa6626da74ca00c7f55b844a94ca00c3fd5ba20a94ca00c6fd5b998a94ca00cff15b844a94ca00cfe95b888a94ca00cfd95b8cca94ca00cbf95ba20a94ca00cef95b998a94ca008ff9bc214a94ca008ff9bc144a94ca00c7f90c26da54ca00c7f9a026da54ca00c7f93026da54ca00c7f92026da54ca00c7f95026da54ca0087fc9c6ad524ca00c7f61126da54ca00c7ee2226da54ca00c7de3326da54ca00c3fe8826da54ca00c6fe6626da54ca008ff89c6ad524ca00cff21126da54ca00cfea2226da54ca00cfda3326da54ca00cbfa8826da54ca00cefa6626da54ca008ff89c6ac854ca008ff89c6ac514ca00e7d5814c4a94ca00e3dd31a20a94ca00e3f611a20a94ca00e6dd31998a94ca00e6f611998a94ca00e2fe88998a94ca00efd1814c4a94ca00efd1214c4a94ca00cff0a946c854ca00cfe8a94ac814ca00cfe8a94ac854ca00cfd8a94ec814ca00cfd8a94ec854ca00cfd8a94ec514ca00cef8a95ac854ca00efd2114c4a94ca00efc931888a94ca00efe211888a94ca00efd2118cca94ca00ebd931a20a94ca00ebf211a20a94ca00ebea22a20a94ca00ebda33a20a94ca00eed931998a94ca00eef211998a94ca00eeea22998a94ca00eeda33998a94ca00eafa88998a94ca008ff8bc845a060a008ff8bc8cda060a00cff0bc845a060a00cfd8bc8cda060a008ffacc4eca960a009fdacc4ec914ca00aff17c2ae1160a00bbf17c22e1160a008ff8bc955a660a00aff0bc69e1160a009fe8bc9556260a00bbf0bc61e1160a00bbf0ac8458160a00cff11c2ae1160a00cff1812ae1160a00cff1212ae1160a00cfe8bc696224ca009fe8bc54e224ca00cf7a552ae1160a00cbfa882ae1160a00cfda332ae1160a00cfba442ae1160a00ef72552ae1160a00ebf2882ae1160a00efd2332ae1160a00efb2442ae1160a008ff8ac46c9360a008ff89c2ad3160a00abf97c2ae884ca00abf8bc69e884ca008ff95c2ae884ca00abf95c2ae884ca008ff8bc8cda160a008ff8bca21a54ca00afd8bc6863360a00abf8bc696884ca00cff2112ae884ca00ebda332ae884ca00ebea222ae884ca00ebf2112ae884ca00ebba442ae884ca009bfacc62c9160a009feacc4ac984ca008ffacc62ca94ca008ffacc46ca960a008ffacc46ca94ca008ffacc56ca94ca00afd96c2ae3360a00bfc96c0ae3360a008ff8bc8cda660a00afd8bc69a3360a009fe8bc8cd6260a00bfc8bc58a3360a0097f89c56d4160a009fd8bc6923360a00dfc8bc60a334ca00cfd9302ae3360a00cfd93c2ae3360a00cfd9322ae3360a00cfea222ae3360a00dfc8bc4c6224ca00cfe8bc686224ca009fe8bc4c6224ca00 else 0xc3fd8126da660a00c77e5526da660a00c7de3326da660a00c5fe7726da660a00cbf98126da660a00cf7a5526da660a00cfda3326da660a00cfea2226da660a00cdfa7726da660a00c7f91b480a960a00c7f55b844a960a00c7ed5b888a960a00c7dd1b8cca960a00c7ed1b888a960a00c6fd5b998a960a00cff15b844a960a00cfe95b888a960a00cfd91b8cca960a00cfe91b888a960a00cef95b998a960a008ff9bc0c4a960a0087fdbc144a960a008ff9bc144a960a00c7f90c26da160a00c7f9a026da160a00c7f92026da160a00c7f98026da160a00c7f91026da160a0087fc9c6ad8160a00c77e5526da160a00c3fe8826da160a00c7de3326da160a00c7ee2226da160a00c5fe7726da160a008ff89c6ad8160a00cf7a5526da160a00cbfa8826da160a00cfda3326da160a00cfea2226da160a00cdfa7726da160a008ff89c6ac3160a0087fc9c6ac5160a008ff89c6ac5160a00e3f561604a960a00e3f531604a960a00e3f551604a960a00e3ed52604a960a00e3f98142ca960a00e7e952480a960a00e3f981480a960a00e7e921480a960a00a7ed2c144a960a00e7e552844a960a00e3f611604a960a00e7f10b844a960a00e7f180844a960a00e7f120844a960a00e7e611888a960a00e3dd818cca960a00e7d6118cca960a00e3ed81888a960a00e76e55888a960a00e6ed52998a960a00e2fd81998a960a00e5fa7742ca960a00e6f611998a960a00e6de33998a960a00ebf161604a960a00ebf131604a960a00cff0a946ca360a00aff11c0eca960a00ebf151604a960a00ebe952604a960a00cbf8a962c3160a00cfe8a94ac3160a00cfe8a94ac5160a00cef8a95aca360a00aef96c0eca960a00cdf8a95eca160a00adf97c06ca960a00efe152844a960a00ebf211604a960a00efe211888a960a00ebd9818cca960a00efd2118cca960a00ebe981888a960a00ef6a55888a960a00ebea88888a960a00efca33888a960a00eee952998a960a00eaf981998a960a00eef211998a960a00eeea22998a960a00eeda33998a960a008ff8bc845a04ca00cff0bc845a04ca009bf8bc8cd8160a00bbd8bc6063360a009feacc4ac9360a00aff17c2ae114ca00bfd17c0ee114ca00aff0bc69e114ca00abf8bc692884ca00bfd0bc5ce114ca00bbe8bc50a884ca00cf7a552ae884ca00cbfa882ae114ca00eb7a552ae884ca00ebf2882ae114ca00efd2332ae114ca00efb2442ae114ca00e9fa772ae884ca0087fc9c46da74ca008ff89c46da74ca0087fd5c26da14ca008ff95c26da14ca0087fc9c46da54ca008ff89c46da54ca00c3fe8826da14ca00c6fe6626da14ca008ff89c6ad214ca00cff21126da14ca00cfea2226da14ca00cfda3326da14ca00cbfa8826da14ca00cefa6626da14ca008ff89c6ac814ca00cff17b844a94ca00))) else (if i<11 then (if i<9 then (if i<8 then 0x9ef8bc606664ca009fe95caed6260a009efacc5aca360a008ff95caeda64ca009feacc4ac3160a00bfd2cc485314ca00cefaaa5ac854ca00ebf211a22aa4ca00eeea6660aaa4ca00eeea6650aaa4ca00eeda664c6aa4ca00eeda665ceaa4ca00ee7a66956aa4ca00eafa66a22aa4ca00eef266846aa4ca00eeea6688aaa4ca00eeda668ceaa4ca00dbda88aed734ca00dfca33aed6260a00deda66aed734ca00dfaa44aed6260a00cefa66aeda74ca008ff91c26da74ca00cf7a5526da74ca0087fc9c5eda660a008ff89c5eda660a0087fd5c26da660a008ff95c26da660a00c6fd6326da660a00c6fd6526da660a00c7f61126da660a00cef96326da660a00cef96526da660a00cff21126da660a00aff0bc692114ca0087fc9c5ada74ca008ff89c5ada74ca0087fd5c26da64ca008ff95c26da64ca00c7f61126da64ca00cff21126da64ca008ff8bc845a460a00aff0bc6921160a0087fc9c62da74ca008ff89c62da74ca0087fd1c26da84ca008ff91c26da84ca0087fc9c62da54ca008ff89c62da54ca00c7f61126da84ca00c6fe6626da84ca008ff89c6ad824ca00cff21126da84ca00cfda3326da84ca00cfea2226da84ca00cefa6626da84ca0087fc9c5ada54ca008ff89c5ada54ca0087fd1c26da54ca008ff91c26da54ca00c77e5526da54ca00c5fe7726da54ca00cf7a5526da54ca00cdfa7726da54ca00cf796b954a94ca00cfd96b8cca94ca00cfe96b888a94ca00cdf96b9dca94ca0087fd1c26da64ca008ff91c26da64ca0087fc9c5ada14ca008ff89c5ada14ca00c7dd3126da64ca00c7f9a026da64ca00c7f92026da64ca00c7f93026da64ca00c77e5526da64ca00c3fe8826da64ca00c7de3326da64ca00c7ee2226da64ca00c5fe7726da64ca00cfd93126da64ca00cf7a5526da64ca00cbfa8826da64ca00cfda3326da64ca00cfea2226da64ca00cdfa7726da64ca00c77d1b954a94ca00c3fd1ba20a94ca00cf791b954a94ca00cbf91ba20a94ca00cfd91b8cca94ca00cfe91b888a94ca00cdf91b9dca94ca008ff9bc204a94ca00c77e5526da14ca00c5fe7726da14ca00cf7a5526da14ca00cdfa7726da14ca00e75e554c4a94ca00e37e55a20a94ca00cdf8a95ec854ca00cdf8a95ec814ca00ef5a554c4a94ca00eb7a55a20a94ca00ef5a558cca94ca00ef6a55888a94ca00edda774c4a94ca00ed7a559dca94ca00e9fa77a20a94ca0087fc9c5eda160a008ff89c5eda160a0087fd5c26da160a008ff95c26da160a0087fc9c56da160a008ff89c56da160a00c7f61126da160a00c6fe6626da160a00cff21126da160a00cefa6626da160a00cff17b844a960a00cfd96b8cca960a00cfe96b888a960a00cef97b998a960a0087fd1c26da660a008ff91c26da660a0087fc9c5ada160a008ff89c5ada160a00 else 0xfee1528466660a00fed173846664ca00fbb2448458160a00fbb1839121160a00fbb1879121160a00faf1838466660a00faf1878466660a00fd6942956774ca00ff9244845314ca00ff9173912114ca00ed7a559dda04ca00eef211999a060a00efb244845a14ca00eef211999a04ca00efb244845a160a00eef1a8846664ca00ed79a6956774ca00ed79a4956774ca00efb1a39121160a00eef1a78466660a00eef1a48466660a00efb1a5912114ca00efb1a7912114ca00efb1a6912114ca00eef1a7846664ca00eef1a4846664ca00efb1a59121160a00efb1a79121160a00efb1a69121160a00fec93188a664ca00f9d931a22774ca00fae98188a6660a00fae98388a6660a00f9e942a22774ca00eeea22999a060a00eeea22999a04ca00eee9a888a664ca00e9f9a1a22774ca00eee9a188a6660a00eee9a488a6660a00eee9a588a6660a00e9f9a5a22774ca00e9f9a4a22774ca00e9f9a6a22774ca00eee9a188a664ca00eee9a488a664ca00eee9a588a664ca00fee21188a6660a00f97a55a22774ca00fee21188a664ca00ff32559121160a00fec9828ce664ca00fec9528ce6660a00fdc9828ce774ca00fad9818ce6660a00fad9878ce6660a00edda339dda04ca00eeda33999a04ca00eed9a88ce664ca00edd9a58ce774ca00edd9a68ce774ca00edd9a18ce774ca00eed9a18ce6660a00eed9a18ce664ca00eed9a78ce664ca00eed9a58ce664ca00eeda33999a060a00eed9a58ce6660a00eed9a78ce6660a00fe6a5588a6660a00fdd2118ce774ca00fe5a558ce664ca00f9da888ce774ca00feca228ce6660a00f9f211a22774ca00feca228ce664ca00fe5a558ce6660a00cefa665eeaa4ca00cef95b99aaa4ca00fb9931912884ca00fb9973912884ca00ff8931912224ca00fba9839122260a00fae942a22664ca00fba9819122260a00fad931a22664ca00fad973a22664ca00efa9a59122260a00efa9a5912224ca00efa9a8912224ca00efa9a69122260a00efa9a19122260a00efa9a6912224ca00efa9a1912224ca00ebb9a1912884ca00eaf9a7a22664ca00eaf9a4a22664ca00eaf9a5a22664ca00ebb9a7912884ca00ebb9a6912884ca00ebb9a5912884ca00ff8a339122260a00faf211a22664ca00ff92339121160a00fbaa889122260a00faea22a22664ca00fbaa22912884ca00ff2a559122260a00ff2a55912224ca00fed2118ce664ca00fada33a22664ca00fbb211912884ca00fed2118ce6660a00efb211912aa4ca00ddea77aed6260a00dafa66aed8160a00cef95b99aaa60a00eeda3399aaa60a00e9fa889deaa4ca009dfacc5ec814ca009dfacc5eca160a008dfcbc696774ca00cdf8bc696774ca009df8bc696774ca008efcbc6866660a00cef8bc6866660a009ef8bc6866660a00daf8bc6066660a00) else (if i<10 then 0xefd2118cda04ca00ef69a8956224ca00ef69a69562260a00efd1a5846334ca00ef69a6956224ca00efd1a8846334ca00efd1a7846334ca00ebd9a68ce884ca00ebf1a4846884ca00efd1a68463360a00efc9a88ce224ca00efc9a58ce224ca00efc9a68ce224ca00efc9a18ce224ca00efc9a58ce2260a00efc9a68ce2260a00efc9a18ce2260a00efd2116863360a00ebd9a18ce884ca00ebd9a78ce884ca00ebd9a58ce884ca00efd2118cda060a00ebf1a7846884ca00efd1a58463360a00efd1a78463360a00ff4a558ce224ca00fbd233846884ca00fbd2888463360a00fb6a889562260a00ff5255846334ca00fbca888ce2260a00fbca228ce884ca00fbe222846884ca00ff52558463360a00cbf95ba22aa4ca00efa94b888a960a00daf96caed8160a00fed1814c6664ca00faf1316066660a00eef1316866660a00def26646ca360a00fed1214c6664ca00fed1414c6664ca00faf1516066660a00fec9824c6664ca00fec9825ce664ca00eee982696664ca00fae93260e6660a00fae9326066660a00fae93261e6660a00deea664ac9360a00fec9424c6664ca00fec9425ce664ca00fae95260e6660a00fae9526066660a00fae95261e6660a00eee952999a060a00eee95269e6660a00d9fa7762c3160a00d9fa7762c9160a00bed91c5ce664ca00eed931999a04ca00eed973696664ca00fad95360e6660a00fdc93150a774ca00edd9319dda04ca00edd93169a774ca00ddda774ec814ca00ddda774ec914ca00ede982696774ca00ede98269a774ca00baf91c61e6660a00eaf981999a060a00ddea774ac9360a00ddea774ac984ca00eaf9876966660a00ddea774ac3160a00ddea774ac814ca00cef98b999a04ca00cdf95b9dda04ca00cdf96b9dda04ca00cdf91b9dda04ca00cef91b999a060a00cef97b999a060a00cef95b999a060a00cef91b999a04ca00cef97b999a04ca00cef95b999a04ca00cefabb998a94ca00cefabb998a960a00aef98c686664ca00aef98c69e664ca00aef98c696664ca00adf95c69a774ca00adf95c686774ca00cdfa776ac984ca00adf96c686774ca00cdfa776ac814ca00cdfa776ac914ca00aef91c69e6660a00aef91c6966660a00cefa666ac9360a00aef97c6966660a00cdfa776ac3160a00cdfa776ac9160a00cdfa772ae1160a00cefa6662eaa4ca00cef98b998a94ca00aef91c69e664ca00aef91c696664ca00aef97c696664ca00cefa666ad524ca00cefa666ac954ca00e67e55998a94ca00e67e55998a960a00cefa662ad3160a00cef93b998a960a00cdfa772ad3160a00cdf98b9dca94ca00cefa6646eaa4ca00cef91b99aaa60a00cdfa7756ca94ca00cef91b998a960a00cef91b998a94ca00cefa662ad5160a00cefa662ad514ca00fee182846664ca00fee142846664ca00 else 0x8ff91c2ae3360a00afd91c2ae3360a00bfc95c0ae3360a008ffacc2ad3160a00c7f6bb844a960a00cfe95b60aaa4ca00cff15b846aa4ca008ff95caeda14ca00cff17b846aa4ca00fbd288605314ca00fbd1214c6884ca00fbd1414c6884ca00fbc95360e2260a00fbc96360e2260a00bbe93c6062260a00dbea884ac3160a00dbea884ac9360a00fbc9424c6884ca00fbc9425ce884ca00ebe981889a060a00ebe98169a2260a00dbea2262c3160a00dbea884ac5160a00dbea2262c9160a00bbd91c5ce884ca00ef69536962260a00dbf28846ca360a00dfca224ec854ca00bbd93c06e884ca00dbda884ec914ca00ebd973696884ca00efc931889a04ca00efc93169a224ca00dfca224ec814ca00dfca224ec514ca00dbda884ec514ca00dfca224ec914ca00dbba8852ca160a00dfaa2252c854ca00dfaa2252ca360a00dfaa2252ca960a00dfaa2252c984ca00dfaa2252ca160a00dfaa2252c814ca00cfe95b889a04ca00cfe98b889a04ca00cfe96b889a060a00cfe91b889a060a00cfe96b889a04ca00cfe91b889a04ca00afe93c6962260a00afe93c69a2260a00afe93c6862260a00afe95c69a224ca00afe95c686224ca00cfea226ac854ca00cfea226ac984ca00cfea226ac954ca00afe96c686224ca00cfea226ac814ca00cfea226ac514ca00cfea226ac914ca00ddea225ec854ca00ddea225ec814ca00afe95c69a2260a00afe95c6862260a00cbfa886ac3160a00cfea226ac9360a00cbfa886ac9160a00afe96c6862260a00cfea226ac3160a00cfea226ac5160a00cfea226ac9160a00dafa885aca360a00ddea225eca160a00cfea222ae1160a00cbfabba20a94ca00cbfa8862eaa4ca00cbfa8862ca94ca00abf90c2ae884ca00cfeabb888a960a00abf91c69e884ca00abf91c696884ca00cbfa886ad214ca00e77655844a960a00cbfa882ad3160a00cbfa886ac914ca00abf9ac06e884ca00abf97c696884ca00cbfa886ad524ca00cbfa886ac514ca00cbfa886ac954ca00abf9ac16e884ca00e77655844a94ca00cfe98b888a94ca00cfe93b888a960a00abf91c2ae884ca00cfea222ad3160a00cfea222ad5160a00cbfa882ad514ca00fbc93188a884ca00ebea88889a060a00ebe9a3a222260a00ebe9a4a222260a00ebe9a1a222260a00ebe9a188a884ca00ebe9a488a884ca00ebe9a688a884ca00ebe9a588a884ca00fbd2114c6884ca00fbd173846884ca00ff4931956224ca00fbd2116063360a00fbd1878463360a00fbca3360e2260a00fb69839562260a00fbe142846884ca00fb69819562260a00fbc9818ce2260a00ef69a49562260a00ef69a4956224ca00efd1a6846334ca00efca33889a04ca00efca33889a060a00ef6a55889a04ca00efd211686334ca00ef6a556962260a00ef6a55696224ca00)) else (if i<13 then (if i<12 then 0xaff15c2ae1160a008ff95c2ae114ca00aff15c2ae114ca00e7b54b844a960a00efb14b844a960a00ffc1814c6224ca00fbe1616062260a00ffc1414c6224ca00fbe1316062260a00fbe1516062260a00efe1316862260a00dfe22246ca360a00dfe22246c854ca00f9da885cd704ca00f9da8861d734ca00f9d9745ce884ca00eee96369a2260a00eee96569a2260a00deea225aca360a00d9fa885eca160a00deea225ac854ca00fb5a555ce884ca00ffc2114c6224ca00fb72558458160a00fb5a554c6884ca00ff61629561160a00fbe2116062260a00fbe21160e2260a00fb6a5550a884ca00efe211889a060a00efe211889a04ca00efe21169a2260a00eb7a5569e884ca00efe21169a224ca00ef71a49561160a00efe21168e2260a00eb7a55686884ca00efe2116862260a00efe2116922260a00efe2116962260a00eb7a55696884ca00eb7a55692884ca00eb7a5569a884ca00efe211686224ca00efe211692224ca00efe211696224ca00ef7255845a060a00ef71a69561160a00efe2222ae1160a00ef7255844a94ca00efe2222ae114ca00ef7255844a960a008ff91c2ae884ca00fbd2334c58160a00fbd1616063360a00fbd1516063360a00fbc98758a3360a00feca3358d6260a00fec96158a3360a00fec97658a3360a00fec96558a3360a00fbc98760a334ca00fbc98160a334ca00fbc9526063360a00fbc98158a3360a00efc982696334ca00efc98269a334ca00bfc95c58a3360a00efd2334c5a160a00ebd9818cda060a00ebd98169a3360a00dfd23346c854ca00dfca334ac854ca00bbd98c06e3360a00dfca334ac984ca00dbda3362c9160a00efc9626863360a00dfca334ac814ca00dfca334ac5160a00eeda3358da660a00eed96569a3360a00cfd91b8cda04ca00cfd95b8cda04ca00cfd96b8cda04ca00cfd98b8cda04ca00cfd97b8cda04ca00afd96c69e334ca00afd97c69a3360a00afd98c69e334ca00afd98c696334ca00afd96c696334ca00afd96c686334ca00ddda335ec854ca00ddda335ec814ca00afd95c6863360a00afd95c69a3360a00afd91c69e334ca00cfd91b8cda060a00cfda336ac814ca00cfda336ac984ca00cfda336ac914ca00afd97c696334ca00cfda336ac854ca00cfda336ac514ca00cfda336ac954ca00deda335ac854ca00cfd96b8cda060a00cfdabb8cca960a00cfda334eeaa60a00cfda334eca960a00afd90c2ae3360a00afd91c69a3360a00cfda336ad8160a00cfda336ac5160a00cfda336ac9160a00afd9ac06e3360a00ddda335eca160a00cfda332ad3160a00cfda332ad5160a00ffc182846334ca00ffc1528463360a00ffc1628463360a00fb5a558ce884ca00fb7255846884ca00ffc2118ce224ca00ff62119562260a00ffc2228463360a00cfd98b8cca94ca00 else 0x8ff98c26da54ca008ff98c26da64ca008ff98c46ca94ca008ff98c26da14ca008ff91c2ad844ca00bbe91c2a1824ca00bbe95c0ad8160a00dfc8bc4c5424ca008ff95c46eaa60a008ff95c46ca960a008ff91c56ca94ca008ff91c2ad654ca008ff8ac5ed4160a008ff95c2ad7160a008ff8ac56d7160a008ff8ac56d4160a00bbf15c2858160a00bbf0ac5458160a00cff1812ad5160a008ff95c2ad714ca00ffc182845314ca00ffc1825ce114ca00fbe16260e1160a00fbe16261e1160a00ef71536961160a00fbe13260e1160a00fbe1328458160a00fbe13261e1160a00df725546ca360a00bfe12c22e114ca00bfe12c0ee1160a00dfe2114ac984ca00dfe2114ac9360a00ffc142845314ca00ffc1425ce114ca00fbe15260e1160a00fbe1528458160a00fbe15261e1160a00efe152845a060a00efe15269e1160a00dfe2114ac854ca00db7a5562c3160a00bfe12c16e1160a00db7a5562c9160a00ff497350a554ca00fbd15360e1160a00ff493150a554ca00ef6982955a54ca00ef593169a554ca00dbf17b8458160a00efd2114c5a04ca00ebf211605a060a00bbf18c0ee1160a00df5a554ec914ca00df6a554ac9360a00df6a554ac984ca00ebf1876961160a00dfd17b845314ca00dfd2114ec854ca00df6a554ac3160a00df6a554ac814ca00cfba1152ca960a00cf7a5556da04ca00cff21146da04ca00cff21146da060a00cff18b845a14ca00aff13c6961160a00cf796b955a54ca00cff13b845a060a00aff13c69e1160a00cf7a556ad214ca00cf7a556ac814ca00cf7a556ac984ca00cf7a556ac914ca00dd7a555ec814ca00df3a5552c984ca00cff17b845a160a00cff15b845a04ca00def2115aca360a00bef16c0ee1160a00dd7a555eca160a00bef16c16e1160a00cff17b845a04ca00dfb21152c854ca00dfb21152c984ca00cff17b845a14ca00cff15b845a060a00aff1ac22e114ca00cff2116ac984ca00aff15c69e1160a00cff2116ad524ca00cff2116ac854ca00aff1ac16e114ca00cff2116ac954ca00def2115ac854ca00bef16c16e114ca00cf7a556ac3160a00cff2112ad854ca00cff17b845a060a00cff2112ad804ca00aff13c2ae1160a00cff2116ac9360a00cff18b844a94ca00bbf13c22e1160a00cf7a556ac9160a00cff13b844a960a00aff1ac0ee1160a00aff18c2ae114ca00aff1ac16e1160a00dfb21152ca360a00df3a5552ca160a00dfb21152ca960a00cff2112ad3160a00cf7a552ad3160a00cf7a552ad814ca00cff2bb844a960a00cff21146eaa4ca00cff2bb844a94ca00cff21146eaa60a00cf7abb954a94ca00cf7a5556ca94ca00cff21146ca960a00aff10c2ae114ca00cff21146ca94ca00aff10c2ae1160a00c77d8b954a94ca00cf798b954a94ca008ff95c2ae1160a00) else (if i<14 then 0x8ff9bc605a060a008ff9bc0c5a060a008ff9bc145a060a008ff91c56da04ca008ff9bc485a04ca008ff9bc205a04ca008ff9bc549a04ca008ff9bc215a04ca008ff9bc145a04ca008ff90c2ad874ca008ff93caeca960a008ff90c2ad6360a008ff90c2ad3160a008ff90c2ad814ca008ff90c2ad654ca008ff90c2ad7160a008ff90c2ad714ca00c77e5556ca94ca008ff90c2ae1160a008ff90c2ae114ca00c7f61146ca960a008ff90c2ae3360a008ff90c2ae884ca008ff91caeca960a008ffacc26da160a008ffacc26da14ca008ffacc26da54ca008ffacc26da84ca008ffacc26da64ca008ffacc26da660a008ff98c46da54ca008ff98c6ad524ca008ff98c6ac514ca008ff98c6ac954ca00cdf9a35eca160a00adf97caeda54ca00cdf9a55ec814ca00cdf9a45ec854ca00cdf9a45ec814ca00cdf9a15ec854ca009df97caed524ca009df97caeda54ca008ff95c6ad8160a00cef9a15aca360a00aef96caeda160a00cdf9a55eca160a008ff95c6ac3160a008ff9acaed3160a008ff9ac26d6360a008ff91c6ac9360a008ff9ac26d3160a008ff9ac26d7160a008ff95c6ac9160a008ff9ac26d5160a00cef9a75aca360a00cdf9a45eca160a00cef9a55aca360a009df97c2ad3160a009ef96caed8160a009ef96caeda160a008ff8ac4ed6060a008ff8ac4ed1060a008ff8ac5ed1060a008ff8ac5ed6360a008ff8ac5ed6460a008ff98c2ad714ca008ff98c2ae114ca008ff91c6ac984ca008ff91c6ad524ca008ff91c6ac854ca008ff91c6ac954ca00cef9a15ac854ca00c7f53b844a960a008ff91c2ad804ca008ff95c6ac814ca008ff91c2ad874ca008ff9ac26d654ca008ff9ac26d814ca008ff9ac26d874ca008ff95c6ac984ca008ff9ac26d854ca008ff9ac26d714ca008ff95c6ac914ca008ff9ac26d514ca00cef9a45ac854ca009ef96caed814ca008ff93c2ad7160a008ff93c2ad5160a008ff95c2ad6360a008ff8ac4ed7160a008ff95c2ad3160a008ff8ac4ed5160a00cbf98b2ad3160a00cbf9832ad3160a00cbf98c2ad3160a00cbf9812ad3160a008ff93c2ae1160a00c7f58b844a94ca008ff91c4eeaa60a008ff93c26da660a008ff93c46ca960a008ff93c26da160a00adf97c2ad3160a00d7b61152ca960a008ff8bc4c5a060a008ff8bc54da660a008ff8bc54da160a008ff91c2ad6360a008ff8ac46d6360a008ff8bc4c5a660a008ff8ac4ed4160a00bfc91c0ed824ca00bfc8bc4c5824ca00cfd9302ad3160a00cfd9322ad3160a00dfc8bc4c5824ca00cfe9322ad3160a00cfe9522ad3160a00cdf97c2ad3160a008ff9bc28ca160a008ff8ac4ec5160a008ff8ac4ec9160a008ff98c56ca94ca008ff98c2ad514ca008ff95c2ad844ca008ff95c2ad814ca008ff91c2ad854ca008ff98c26da74ca00 else 0xfae96160d6260a00fae97660d6260a00fae96560d6260a00fae98758d6260a00fae9875856260a00fae9875956260a00ebe987609a64ca00dbe98756d6260a00ebe987609a54ca00ebe983609a54ca00ebe983609a64ca00dbe98356d6260a00d9f9835eca160a00bbe98c0ed6260a00bbe98c0ad314ca00dbe9874ac3160a00dbe9874ac9360a00dee9425ac854ca00fbc9815cd824ca00fbc9814c5824ca00ebe981609a54ca00bbe92c0ed8160a00ebe952605a060a00dbe9814ac9360a00dbe9814ac984ca00dee9525aca360a00bbe93c0ad8160a00bbe98c285824ca00bbe92c16d8160a00dbe95262c3160a00dbe9834ac5160a00dbe93262c9160a00dbe95262c9160a00efc973609a54ca00fdc9825cd704ca00fdc97b5cd824ca00bdcd7c0ed824ca00fdc98261d734ca00fdc9825d1734ca00bfc97c4c5824ca00bfc97c0ed824ca00bfc8bc5cd824ca00dfc9734ac984ca00fdc94261d734ca00bfc97c4c5424ca00dfc9734ac814ca00ded9835aca360a00ded9315ac854ca009fd91c4ec854ca00dfc9424ec854ca00bfc93caed824ca00cfd93b4c2aa60a00afd93caeda84ca00cfd9324eeaa60a009fd93caeda460a009fd93c26d714ca00bfc92c22d314ca00dfc9314ac854ca00bfc92caed314ca00dfc9314ac9360a00dfc9314ac984ca00cfdabb4c4a94ca00cfd9316ac854ca00bdd97c22d314ca00ddd9315ec854ca00bfc98c0ad314ca00afd8bc4c5a04ca00bfc93c06d824ca00afd93c215a04ca00cfd9a14ec854ca00cfd9a44ec854ca00dfc9424ec814ca00afd93c205a04ca00cfd9a54ec814ca00dfc9824ec514ca00dfc9424ec514ca00afd93c145a04ca00cfd9a84ec514ca00dfc9824ec914ca00cfe9826ad524ca009bf98c4eca160a00cfe9826ac954ca00cfe9826ac514ca00dde9325eca160a009bf98c46ca360a00afe8bc609a54ca009fe95c4ac9360a009fe95c4ac3160a00cbfabb604a960a00daf9815aca360a00baf96caed8160a00dde9525eca160a00abf8bc605a060a00abf98c0c5a060a00afe92c215a04ca00cfe9a44ac854ca00cfe9a14ac854ca00afe92caeda14ca009fe92caeda14ca00afe92caeda54ca009fe92caeda54ca009fe92caed7160a009bf98c26d3160a009fe92c26d6360a00cfe9a54ac984ca009bf98c26d7160a00daf9875aca360a00cfe9426ac854ca00dde9425ec854ca00dde9425ec814ca00afe92c0c5a060a00afe92c205a04ca00cfe9a54ac814ca00afe92c145a060a00aef96c0eda060a008dfd7c2ad3160a00aef96c28da060a00adf97c215a04ca00c7be1152ca960a008efd6caeda160a008dfd7caeda54ca00adf97c06da060a00adf97c285a060a00aef96c215a04ca00adf97c205a04ca008ff98c56da04ca008ff9bc4c9a060a008ff95c46da060a00)))) else (if i<23 then (if i<19 then (if i<17 then (if i<16 then 0xcfba445ada160a00cfba445eda160a00cfba446ad8160a00cfba446ac5160a00cfba4446da74ca00cfba445ada14ca00cfba4446da54ca00cfba446ac814ca00cfba442ad5160a00cfba445ada74ca00cfba445eda54ca00cfba445ada54ca00cfba446ac854ca00cfba446ac514ca00dfb24446c854ca00cfba444eeaa60a00cfba442ad3160a00fb9a446063360a00ff8a4458a3360a00ef9a446863360a00ef9a4469a3360a00ffa1329121160a00ffa1629121160a00ffa1529121160a00ffa2119122260a00fb3a55912884ca00fa7a55a22664ca00ffa211912224ca00fe72558466660a0097becc52ca960a009fbacc52ca960a00a7becc52ca960a00afbacc52ca960a009fbacc52ca160a00fbc5814c5824ca00ffc11b4c5824ca00ffc1814c5824ca00bfc51c0ed824ca00fae5616056260a00fbe1614c98160a00fbe1316056260a00efe131589a160a00fbe1314c98160a00dfe16246ca360a00ffc131485204ca00ffc162485314ca00ffc182485314ca00ffc1814c5424ca00ffc142485314ca00fbe1615498160a00fbe1315498160a00dfe15246ca360a00fbd1316053060a00fbd1634c58160a00efd1316853060a00efd1634c5a160a00efd1814c5a04ca00fbd131605804ca00fbd186605314ca00fbd1324c58160a00bfd18c485314ca00bfd18c285314ca00bfd11c2a1314ca00bfd11c28d3060a00dfd13246ca360a00ebf161605a060a00faf1815856060a00faf1625858160a00bbf16c4c58160a00bbf16c5458160a00bbf13c5458160a00ebf131605a060a00ebf131605a660a00cff1316ad8160a00bbf13c2858160a00cff13b684a160a00dbf18c46ca360a00bbf11c28d8160a00dbf18746ca360a00aff11c28da060a00cff1a646ca360a00cff1ac46ca360a00cff1a746ca360a00cff1a546ca360a00bbf0ac4c58160a00cff1a12ad3160a00cff1812ad3160a00ebf0ac4c58160a00cff11c2ad3160a00efd1214c5a04ca00efd1214c5a64ca00cff1212ad3160a00bbf11caa98160a00aff11caeda160a00cff18146eaa60a00cff12146eaa60a00cff13146ca960a00bfd11c261314ca00bbf11c24d8160a00aff11c24da160a00cff17146ca960a00ffc1414c5824ca00efd1414c5a64ca00fbe1516056260a00fbe1514c98160a00fb69515498160a00ebf151605a060a00ebf151605a660a00dbf15162c9160a00bbf11c2958160a00dfe14246c854ca00dfd13c46c854ca00bfd11c215314ca00aff11c215a04ca00cff1ac46c854ca00aff11c215a14ca00cff1a446c854ca00bbf11c14d8160a00aff11c14da160a00af795c205a54ca00bbf11c2558160a00f9cd8261d734ca00fbc96360d824ca00fbc9874c5824ca00fbc98c4c5824ca00fbc93160d824ca00bbcd8c0ad314ca00fae96360d6260a00 else 0x87fd8c26da14ca0087fd8c26da64ca00c3febb604a960a00bf994c28d3060a00df997352c984ca00df997352c814ca00df993152c854ca00bf994c22d314ca00df993152c984ca009fb94c2ad5160a00dbb98352ca160a00dbb98752ca160a009fb94c2ad3160a00dbb98152ca360a00dfa96252ca360a00afb94c28da060a00cfb9a652ca360a00cfb9a152ca360a00dbb98152ca960a00dfa93252ca960a00dfa96252ca960a00cfb9a352ca960a00cfb9a652ca960a00cfb9a152ca960a009fb94c26e3360a00afb94c06da060a00dfa95252ca160a00dfa93252ca160a00afb94c285a060a00cfb9a552ca160a00cfb9a352ca160a00cfb9a752ca160a00cfbabb52ca960a00cfb9a152c984ca00cfb9a152c854ca00cfb92152ca960a00cfb95152ca960a00b79d4c26e3360a00cfb9a752c814ca00cfb9a752c984ca00cfb9a552c814ca00cfb9a552c984ca00cfb98152ca960a00cfb93b52ca960a00cfb94c2ad3160a00df9a3352ca160a00df9a3352ca960a00bf994c06e3360a00bf994c26e3360a00c7bd7b52ca960a00cfb96b52ca960a00c7bd1b52ca960a00cfb91b52ca960a00e3bd4b604a960a00cfb8a952ca360a00ebb94b604a960a00afb94c0eca960a00cfb8a952ca160a00afb94c06ca960a00ef994b8cca960a00c6fd8b998a94ca00c6fd1b998a960a00c6fd1b998a94ca00fe695154a6660a00fe697554a6660a00fe695354a6660a00c6fd3b998a960a00ee79536966660a00fdd1414c6774ca00fdd1814c6774ca00ddf27746ca360a00fa7a556066660a00fa7a5561e6660a00fa7a5560e6660a00fde21150a774ca00fe6a5554a6660a00fdd2114c6774ca00fe5a554c6664ca00fe5a555ce664ca00ee7a55696664ca00ee7a55686664ca00ee7a55692664ca00edf211686774ca00edf2119dda04ca00ee7a556866660a00edf211692774ca00edf21169a774ca00ee7a55999a060a00ee7a556966660a00ee7a5569e6660a00ee7a556926660a00edf2772ae1160a00edf277844a94ca00ee7a55998a94ca00edf2772ae114ca00ee7a55998a960a00c5fe77aeca960a00ff9244605314ca00ff9244485314ca00df9a445ed314ca00ff8a445cd824ca00ef9a445cda54ca00ff8a444c5824ca00ef9a444c5a64ca00df9a444ec854ca00df9a444ec514ca00df9a444ec814ca00fbaa4460d6260a00fbaa4461d6260a00fbaa445498160a00fbaa444c98160a00fbaa446056260a00fbb2444c58160a00efb2444c5a160a00fbb2445858160a00fbb2445458160a00ebba44605a660a00efaa44609a54ca00dfaa4456d6260a00efaa44609a64ca00dfaa444ac854ca00efaa44589a160a00dfaa444ac5160a00dfaa444ac814ca00cfba4456da160a00cfba4462da74ca00cfba4462da54ca00cfba445eda660a00) else (if i<18 then 0xfcba449de664ca00ddba7752ca160a00ddba7752c814ca00feb244846664ca00fd3a44956774ca00feb2669121160a00d5be7752ca960a00deba6652ca960a00e5be7752ca960a00eeb94b998a960a00ddba7752c984ca00fd9a444c6774ca00fd9a4461d734ca00fe9a445ce664ca00fe9a444c6664ca00faba4460e6660a00faba4461e6660a00faba446066660a00feaa4454a6660a00feaa4460a664ca00eeba446966660a00eeba44696664ca00eeba446a2664ca00eeba4469e6660a00eeba446866660a00eeba4469e664ca00eeba44686664ca00edba44686774ca00feaa445956260a00eeba44595a660a00ddba445eca160a00edba4469a774ca00edba44696774ca00ddba445ec814ca00feaa4458d6260a00eeba4458da660a00fe9a448ce6660a00faba66912884ca00f8ed875d96260a00fcda665cd704ca00fcd9875ce664ca00fcda664c6774ca00f8fa7760e6660a00f8fa776066660a00fcea6650a774ca00ecfa77999a060a00ecfa77999a04ca00ecfa776a2664ca00ecfa776926660a00ecfa776966660a00ecfa77686664ca00ecfa77692664ca00ecfa77696664ca00f8f97361e6660a00ecf97369e6660a00dcfa775aca360a00f8f97161e6660a00ecf97169e6660a00fc7a66956774ca00fcf2778466660a00fdb277912114ca00fcf277846664ca00fdb2779121160a00fcda778ce664ca00fcda778ce6660a00feaa669122260a00feaa66912224ca00f8fa77a22664ca00f9ba77912884ca00ecfa7799aaa60a00e4fe77998a960a00ecfa77998a960a00ecfa77998a94ca00ecfa669deaa4ca00eeba66912aa4ca00eeba4499aaa60a00feaa445d96260a00fcd9745ce664ca00feaa445856260a00f8f97561e6660a00deba6652ca360a00deba445ac854ca00ddba445ec854ca00d3bd8152ca960a00d3bd8752ca960a00c7f53146ca960a0093fd8c26d3160a00c7f57146ca960a00c7bda152ca960a00c7bd2152ca960a00c7bda752ca960a00c7bd5152ca960a0097bd4c26e3360a0087fdac26d814ca0087fdac26d874ca0087fdac26d854ca0087fdac26d514ca0087fd8c56ca94ca0087fdac26d654ca0087fd8c46ca94ca00c7bd8152ca960a0087fdac26d3160a0087fdac26d5160a0087fd3c46ca960a0087fd5c46ca960a0087fd1c56ca94ca00fb65515498160a0087fd3c26da160a0087fd3c26da660a00fb71655458160a00ff61515491060a00fb71525458160a00ddf1215eca160a00ff615354a1160a00ff617554a1160a00fb72555458160a00fe6a555956260a00fdd2115cd704ca00ee7a55595a660a00f9f17561e1160a00f9f17661e1160a00fdd1745ce114ca00f9f17361e1160a00fdd1875ce114ca00edf17369e1160a00ddf2115ec854ca00de7a555aca360a0087fd8c26da54ca00 else 0xf3ed52604a960a00e7ed52684a960a00e3fd85604a960a00a7fd5c684a960a00e3fd53604a960a00a7fd2c544a960a00e3fd52604a960a0097fc9c4ad654ca0097fc9c62d714ca0097fd5c26d814ca00d7f55126d814ca009bfcbc8cd8160a0097fc9c6ad514ca00c7fd8526da14ca00c7fd8156ca94ca00d7ed8226da54ca00d7dd3126da54ca00c7fda626da54ca00c7fda826da54ca00c7fd8326da54ca00c7fd8226da54ca00c7fd8126da54ca00c7fda126da54ca00c7fd3126da54ca00c7fd2126da54ca00e7f581544a94ca00e7dd854c4a94ca00a7fd8c544a94ca0097fc9c4ed654ca0097fd1c26d534ca0097fd5c26d3160a0097fc9c4ed5160a0097fc9c4ed514ca00d7dd3126d534ca00c7fda626d534ca00c7fda126d534ca0097fd1c26d854ca0097fc9c62d514ca0097fc9c4ad5160a0097fc9c4ad514ca008ffcbc8cda160a00d7dd3126d854ca00c7fda126d854ca00d7dd7326d814ca00c7fda726d814ca00c7fda526d814ca0097fd1c26d654ca0097fc9c46d654ca0097fc9c56d7160a0097fc9c56d714ca008ffcbc8cda660a00d77d5126d654ca009fecbc8cd6260a00d7ed8226d514ca00c7fda826d514ca00d7ed3226e1160a00d7ed5226e1160a00d3fd8326e1160a00c7fda326e1160a00c7fda526e1160a00a7fecc614a94ca00cff6aa46c854ca00cdfeaa5ec854ca00adfd7c22eaa4ca00cfdeaa4ec854ca00cffaaa42c854ca00cfeeaa4ac854ca00c7feaa26d854ca00c7feaa26d514ca00c7feaa26e554ca0097fd1c26e884ca008ffdbc146aa60a00cfbeaa52ca360a00cfbeaa52ca160a008ffecc6ac854ca00d3fd8126e3360a00c7fda126e3360a0097fecc26d5160a0097fd5c26e884ca008ffd3caeda84ca008ffdbc0c6aa60a00d7dd3126e884ca00d7dd7326e884ca00c7fda126e884ca00c7fda726e884ca00cffaaa42ca360a00cff6aa46ca360a00cdfeaa5eca160a00cefeaa5aca360a00c7feaa26d5160a00c7feaa26e884ca008ffecc6ac3160a0097fc9caed5160a0097fc9caed514ca008ffecc6ad824ca008ffecc6ac5160a008ffd3caeda160a00c7fd8526eaa4ca00c7fd8126eaa4ca008ffd3caeda660a00c7fd754eca960a00c7fd7346ca960a00c7fd714eca960a00c7fd8726da14ca00c7fd8726da64ca00c7fd6226da54ca00c7fd7326da160a00e3fd73604a960a00c7fd6326da54ca00beecac58d6260a00cefd622ad6360a00cbfd872ad6360a009bfcbc5958160a00faed321ad8160a00faed521ad8160a00beecac5956260a00cdfd872ad7160a00cdfd872ad714ca00cfed822ad714ca009fecbc5c56260a00d5fd7126d874ca00d7dd3126d654ca00c7fda126d654ca00c7feaa26d654ca00dafc5b1ad8160a00cff51b06eaa60a00cfdd3b0eeaa60a00fcba449de6660a00)) else (if i<21 then (if i<20 then 0x770058002c0000d7bd5152ca960a0097fd5c46ca960a00c7fd514eca960a0097fd8c26da54ca00c7fd5162ca94ca0097fd8c26d514ca00dbbd8152ca360a00dfad6252ca360a00cfbda652ca360a00cfbda152ca360a00dfad5252ca160a00cfbda552ca160a00ffc51b4c5824ca00ffc5814c5824ca00fbe5614c98160a00fbe5314c98160a00dfe56246ca360a00ffc582485314ca00fbe5615498160a00fbe5315498160a00dfe55246ca360a00dbf58746ca360a00cff5a646ca360a00cff5a746ca360a00cff5a546ca360a00fbe5514c98160a00fbcd6360d824ca00fbcd874c5824ca00fbcd3160d824ca00faed6360d6260a00faed6160d6260a00faed7660d6260a00faed6560d6260a00faed8758d6260a00faed875856260a00faed875956260a00ebed87609a64ca00ebed83609a54ca00ebed83609a64ca00dbed8356d6260a00d9fd835eca160a00bbed8c0ed6260a00fbcd815cd824ca00ebed81609a54ca00bbed2c0ed8160a00deed525aca360a00bbed8c285824ca00bbed2c16d8160a00dbed5262c3160a00dbed834ac5160a00fdcd7b5cd824ca00fdcd8261d734ca00bfcd7c4c5824ca00dedd315ac854ca00bfcd3caed824ca00afdd3caeda84ca00cfdd324eeaa60a00dfcd314ac854ca00cfdd316ac854ca00dddd315ec854ca00dfd93142c854ca00bfcd3c06d824ca00cfdda14ec854ca00dfcd824ec514ca00cfdda84ec514ca009bfd8c4eca160a00cfed826ac514ca00dded325eca160a00dafd815aca360a00dded525eca160a00dbf98142ca360a00cfeda14ac854ca009fed2caed7160a00dafd875aca360a00dfe96242ca360a008ffd8c6ac514ca00cdfda35eca160a00cdfda15ec854ca009dfd7caed524ca009dfd7caeda54ca00cefda15aca360a00cdfda55eca160a00cefda75aca360a00cff9a642ca360a00cefda55aca360a00cff9a142ca360a009dfd7c2ad3160a009efd6caed8160a009efd6caeda160a008ffcac5ed6360a008ffd8c2ad714ca008ffd8c2ae114ca00cefda15ac854ca00cff9a142c854ca00c7fe554eca960a009efd6caed814ca008ffd3c2ad7160a008ffcac4ed7160a008ffcac4ed5160a008ffd3c2ae1160a008ffcac46d6360a00cfed522ad3160a00cefeaa5ac854ca0097fd5c26da64ca0097fd1c26d874ca0097fc9c6ad854ca0097fc9c6ad654ca0097fd1c26da54ca00c7fda526da64ca00c7fd5226da64ca00c7fd5326da64ca00c7fd8546ca94ca0097fd5c26da160a0097fc9c6ad5160a00d3fd5b604a960a00c7fd5b684a960a00c7fd5246ca960a00c7fd5346ca960a00c7fd8546ca960a00b7ec9c56d824ca00d7ed5226da160a00c7fda526da160a00c7fd5226da160a00c7fd5326da160a00c7fd8526da160a00f3f551604a960a00e7f581544a960a00 else 0x23ce23c923c423bf23ad23a823a32391237f236d235b23562351234c23472342233d233823332321231c230a2305230022fb22f622f122df22da22d522d022cb22c622b422af22aa22a522a0229b2289227722722253224121c721b521a32136211720b720b220522040202e1fa71f951f761f711f521f4d1f3b1f291f241f1f1f0d1efb1ef61ef11eec1eda1ec81eb61eb11eac1ea71ea21e901e8b1e861e811e7c1e771e721e601e4e1e491e441e3f1e3a1e281e231e1e1e191e141e0f1e0a1e051e001dfb1df61df11dec1de71de21ddd1dd81dc61dc11dbc1db71db21dad1da81da31d9e1d991d941d8f1d8a1d851d801d7b1d761d711d6c1d671d621d5d1d581d531d4e1d491d441d3f1d2d1d1b1d091cf71ce51ce01cce1cc91cc41cb21cad1ca81ca31c9e1c991c941c8f1c8a1c851c801c611c4f1c3d1c2b1bb11b9f1b4c1b3a1b281b161b041af21a6b1a5919b819a6199418f318e11840182e181c180a17f817e617e117dc17ca17c517c017bb17b617a41737172516c516b316a1168f160815f615e415d215cd15c815c315be15b9159a15951590158b158615811562155d153e152c151a14fb14f614f114d214cd14c814c314be14ac149a14881476146413ea13cb13ac1332130612da126d124e122f1210120b11f911e711d511d011cb11c611c111bc11b711a511a01174116211431131111210f310e110cf10bd10b810a61094107510561037102510060ff40fd50fb60fb10f9f0f8d0f880f690f640f5f0f400f210f0f0ef00ede0ecc0e860e740e550e360e240e050df30de10ddc0d890d770d720d6d0d680d630d440d250d130d010cef0cdd0ccb0c9f0c800c610c420c230c110bff0bed0bdb0bbc0baa0b980b860b810b7c0b5d0b580b460b340b150b030ae40ac50aa60a870a750a630a440a320a200a0109fc09f709f209c609b409a20990097e096c094d092e091c09170912090d0908090308fe08ec08da08bb089c088a08850880087b08690857085208400821081c08170812080007fb07f607f107ec07e707e207dd07d807d307ce07c907c407bf07ba07b507b007ab07580753074e07490744073f073a07350730072b07260721071c07170712070d0708070306fe06f906f406ef06ea06e506b906b406af06aa06a506a0069b06960691068c06870682067d0678064c062d060105c8059c05970592058d05880583057e05790574056f056a054b053905340508050304fe04f904f404ef04a904970485046604470442043d04380433042e041c04170412040d0408040303fe03ec03e703d503d003cb03c603c103bc03b703b203ad03a803a3039e03990394038f038a03850380036e03690364035f035a03550350034b032c031a030802dc02bd0291024b021f01e601c701a8017c015d0131011200f300c700a80089) else (if i<22 then 0x41274122411d410b4106410140fc40ea40e540d340c140bc40b740b240ad40a840a3409e40994094408f408a40854080407b40764064405f401940073fb43fa23f763f4a3f383f263f143f0f3f0a3ed13ebf3e6c3e5a3e483e433e313e2c3dd93dc73d743d623d1c3d0a3cf83ce63cd43ccf3cca3cc53cc03c7a3c683c153c033bf13bdf3bda3bd53bd03bcb3bc63bc13b6e3b5c3b093af73ae53ad33ac13aaf3a9d3a8b3a793a673a553a433a3e3a393a343a2f3a2a3a183a063a0139fc39f739f239ed39db39c939b739b239ad399b399639843972396d39683963395e39593954394f38fc38ea38973885383f382d381b3809380437ff37fa37f537f037eb377e376c36ff36ed36a7369536833671365f365a36553650364b363936273615360335f135df35da35d535d035cb35c635b4356e355c354a353835263514350234af349d348b3479346734553443343e34393434342f342a341833d233c033a133753356333733253313330e32fc32c332b1329f329a32953290328b3279326732553250323e322c32273222321031fe31ec31cd31ae319c318a316b314c313a311b30fc30ea30d830d330ce30c930c430b230ad30a830a33091308c30873082307d306b305930543042303d30383033302e30293024301f301a30153010300b300630012ffc2ff72fa42f922f3f2f2d2ee72ed52ec32eb12e9f2e9a2e952e902e8b2e862e742e6f2e6a2e652e532de62dd42dcf2dca2dc52db32da12d8f2d8a2d852d802d7b2d762d642d522d402d2e2d1c2d0a2cf82ca52c932c812c6f2c5d2c4b2c392c342c2f2c2a2c252c202c0e2bfc2bc32bb12bac2b9a2b952b902b7e2b6c2b5a2b482b362b242b122b002aee2ae92ae42adf2ada2ad52ad02acb2ac62ac12abc2ab72ab22aad2a9b2a892a842a7f2a6d2a682a632a5e2a4c2a472a352a302a2b2a262a212a1c2a172a122a0d2a082a0329fe29f929f429ef29ea29a4295e295929542942293d292b29192914290f290a2905290028fb28f628f128ec28da28c828b628a4289f289a288828832871286c285a28552850283e28392834282f282a28252820281b28162811280c2807280227fd27f827f327ee27e927e427df27da27d527b627a427922780277b27692764275f274d273b27292724271f271a2715271026fe26f926f426ef26ea26e526d326ce26c926c426bf26ba26a826a3269e268c267a2668265626442632262d261b26162611260c2607260225fd25f825f325ee25e925e425df25da25d525d025cb25c625c125bc25b725b225ad25a825a3259e258c25872582257d257825662561254f2530251124f224e024db24d624d124cc24ba24b524a3249e24992494248f248a247824662461245c244a24452440243b24362431241f240d23fb23f623f123ec23e723e223dd23d823d3 else 0x595f594d59485929591758f858e658d458cf58ca58c558c058bb58b658a4589f589a58885876586458525840583b58365831581f580d57fb57e957d757c557b357a1579c578a57855780577b57695764575f574d573b572957175712570d5708570356f156ec56e756e256dd56d856d356c156bc56b756b256ad56a856a3569e568c56875682567d56785666565456425630561e560c560755f555e355d155bf55ad559b558955775565555355345515550354f154ec54e754e254d054b154ac54a754a254835471546c545a54555450544b54465441543c542a54255413540153fc53f753f253ed53db53d653c453bf53ba539b5389537753655353534e53495344533f533a53355316530452ff52d352b452af52aa52985293528e527c526a52655260524e523c522a5218520651f451e251d051be51ac519a518851835171515f514d513b51295117510550f350e150cf50ca50c550c050bb50b650b150ac508d507b50695057503850265014500f4ffd4fde4fcc4fc74fc24fb04fab4fa64fa14f9c4f974f924f804f614f5c4f4a4f384f334f2e4f294f174f124f0d4f084f034efe4ef94ee74ed54ed04ebe4eb94eb44e954e904e8b4e864e744e6f4e5d4e4b4e464e414e3c4e374e0b4df94df44de24ddd4dd84dc64db44daf4daa4da54d934d814d6f4d5d4d4b4d394d274d154d034cf14cdf4ccd4cc84cc34cb14cac4c9a4c954c834c714c5f4c5a4c554c434c3e4c394c344c2f4c2a4c254c204c0e4c094c044bf24bed4bdb4bc94bc44bbf4bad4ba84ba34b914b8c4b874b824b7d4b784b734b6e4b694b644b5f4b5a4b554b504b4b4b464b344b2f4b1d4b0b4b064b014afc4aea4ad84ad34ace4abc4aaa4a984a934a8e4a894a774a654a534a414a2f4a1d4a0b4a0649f449e249d049be49ac499a49884976496449524940492e491c490a48f848d948ba48a84896488448724860484e482f482a48184806480147ef47d047be47b947b447af47aa479847794767474847434731472c47274722471d470b470646f446e246dd46d846ac46a7466e46694664465f465a46554650463e463946274615460345f145df45cd45bb45a94597458545734561454f454a454545334521451c45174512450d450844f644e444df44da44d544d044be44b944b444a24490447e446c445a44554443443e4439443444224410440b4406440143fc43f743e543e043db43d643d143bf43ad439b4389437743654353434e43494344433f433a43354330431e43194307430242fd42f842f342ee42e942e442df42da42d542d042be42ac429a42884276426442524240422e421c42174212420041fb41f641f141ec41e741d541d041cb41b941b441af41aa41a541a0419b41964191418c41874182417d41784173416e41694164415f415a41554143413e4139))) else (if i<27 then (if i<25 then (if i<24 then 0x85e785e285d085cb85c685b485a2859d859885938581857c856a856585608541853c85378532852d850184ef84dd84cb84c684b484a28490848b84868481847c8477846584608441842f842a83ca83ab83998394831a830882f682e482d282c082ae829c828a82788266825482428223821181ff81e081ce81af819d818b8179815a8155813681248112810080ee80dc80ca80ab80998087807580568051804c802d800e7ffc7fea7fd87fb97fa77f887f837f7e7f797f747f487f297f0a7ef87ee67ec77ea87e897e6a7e4b7e397e0d7dfb7ddc7dbd7dab7d997d877d757d567d447d257d067ce77cc87ca97c977c787c667c547c287c097bf77b977b857b667b477b357b307b1e7b0c7afa7ae87ac97aaa7a8b7a6c7a5a7a487a297a0a79f879d979ba79a8799679847965795379417922790378f178df78cd78ae78a9788a786b7859784778357823781177ff77e077db77c977b7779877867774776277507731771f770d76ee76cf76b0769e7672765376347622760375e475c575b375a1758f758a756b754c752d7528751674f774cb74ac748d747b745c743d742b740c73e073c173af7390737173527333731472f572d672b7729872937274725572367224720571d971ba719b717c715d713e711f710070e170c270a3708470727053703470156ff66fd76fb86f996f876f1a6f086ee96e6f6df56d7b6d696d576d386d196ced6cce6ca26c836c716c5f6c336c146bf56bc96baa6b8b6b796b5a6b486b366b246b126b006aee6adc6aca6ab86aa66a946a756a566a446a326a206a0e69fc69ea69be699f698d696e695c693d691e690c68fa68e868d668c468986879685a683b681c680a67eb67bf67a06781675567296717670566e666d466c266b0669e668c667a665b664966376625661365f465e265c365b1659f658d656e655c653d652b651964fa64db64c964aa648b6479646764486436641763eb63d963ba63b563a3637763726360634e633c632a6318630662f462e262c362a4629262736261624f6230622b621961ed61ce61af61906164614560ff6085603f602d601b60095ff75fe55fd35fc15faf5f905f715f5f5f5a5f555f435f315f1f5f0d5efb5ee95eca5eb85e995e945e8f5e8a5e6b5e665e615e4f5e3d5e2b5e195e145e0f5e0a5df85de65dd45dc25dbd5dab5da65da15d9c5d8a5d785d665d545d425d305d1e5d195d075cf55ce35cd15cbf5cad5c9b5c895c775c655c535c415c2f5c1d5c0b5bf95bda5bc85bb65ba45b925b735b615b5c5b575b525b4d5b485b435b3e5b2c5b0d5b085b035afe5af95ae75ae25add5ad85ac65ac15abc5aaa5a985a935a8e5a7c5a775a725a6d5a685a565a515a4c5a3a5a355a305a1e5a195a145a0f5a0a5a055a0059fb59dc59a3599e598c59875982597d59785973596e59695964 else 0x7a43422834888c2c22a3b7b8b7a6b787b775b756b72ab6feb6dfb6b3b67ab65bb62fb61db5feb5ecb5cdb5aeb59cb57db55eb532b513b4e7b4bbb482b470b45eb44cb447b428b423b41eb40cb3fab3e8b3d6b3c4b3bfb3bab3b5b3a3b39eb38cb37ab368b349b344b332b320b31bb309b2eab2beb29fb29ab27bb25cb23db22bb20cb1fab1f5b1d6b1d1b1bfb1adb19bb189b16ab14bb12cb10db0fbb0e9b0d7b0b8b099b07ab05bb03cb010afe4afc5afa6af7aaf4eaf2faf10aef1aeb8ae99ae7aae5bae3cae1dadfeadc5ad7fad46ad27acfbacc2aca3ac91ac72ac60ac4eac3cac10abe4abc5aba6ab94ab82ab63ab37ab0baaecaacdaabbaa9caa70aa44aa25aa06aa01a9d5a9b6a997a96ba94ca92da8f4a8c8a8a9a88aa86ba866a861a84fa830a804a7e5a7c6a7a7a788a769a73da704a6e5a6c6a6a7a695a690a664a645a626a607a5e8a5c9a5aaa58ba56ca54da52ea50fa4f0a4d1a4bfa4a0a48ea46fa443a424a405a3e6a3c7a3a8a3a3a39ea38ca36da35ba349a337a318a2eca2cda2aea28fa270a251a232a213a1f4a1d5a1b6a197a178a159a13aa11ba109a0dda0bea09fa073a054a042a023a0049fe59fc69fa79f889f699f4a9f2b9f0c9eed9ece9eaf9e909e649e389dff9dd39db49d959d769d579d389d199cfa9cf59cd69cd19cbf9ca09c749c559c299c179c059be69bc79ba89b899b779b589b399b1a9b159b039afe9af99af49aef9aea9ae59ae09ace9ac99ab79ab29aad9a9b9a899a779a659a539a419a2f9a1d9a0b99f999e799e299dd99d899d399ce99c999b799a599a0999b99969991998c997a9975997098f698e498d298c098ae989c988a98859873986e985c98579852984d984898439831982c981a9808980397fe97f997f497ef97ea97e597e097db97d697d197cc97c797c297bd97b897b397ae97a997979792978d97889783977e9752972696ed96b49688964f961695f795cb9592953f94ec9499944693f393a0934d931492c1926e921b91bb9168911590c2906f905d904b90399034902f902a9025901390018fef8fea8fd88fc68fc18faf8f9d8f988f938f408eed8ea78e958e768e648e458e268e078de88dd68db78da58d938d748d628d508d3e8d1f8d008ce18ccf8cbd8cab8c8c8c7a8c688c498c2a8c188bf98be78bd58bb68ba48b928b808b6e8b5c8b4a8b388b198afa8adb8ac98aaa8aa58aa08a9b8a968a508a3e89f889e689ad898e897c895d893e891f891a890888f688e488df88da88d588c388b1889f889a889588838871885f884d883b88298817880587f387ee87e987e487d287cd87c887c387be87ac87a787958790878b87868781877c875d875887468734872f871d8718870686f486e286d086cb86c686c186bc86b786b286a0869b8696868486728660864e863c862a86188606) else (if i<26 then 0xc001b030407800900a000802a001026002203da1053818301378008101378008102c0c0b020078003e0008000f0004c0a1b030400003c00100000001a121f000400003c0010000000000000000000042104000000000000000000000000000000000441431070941c32050f80020f000400f0004000000000000d0304545e000f8003e00080f0012015000813001011970804793702081500a005803111080b66f0007c001b0304202108104028002020001009400501bb842a2212555c04201400100540800040250017e0204b01e085ac20cb0306c0c101e00500040150008100008037026002005ce1063818203c00a000802a001020001009400501b8859c20c7030440c130305e00178004007800400000200100a0008080004096b84023c12545c0420090010010007f0110b0130fe000f8003606080f00120140010054002040002384023ca70306c0c190304000001013780080000010137800810137800824c109286026f0010010137800800002058181604240181606058101e005002a040025012dc0c01302627c0011413818226201e005408004a0263818028013025a7c0011408a8dc0c1140898c078014020012809601570801311e0008a09c0c115138182262004b4212d0849820000000780020041bc28104378085e1608213c0420b1046080da08c13c042f020f80020f0007c001f00042451058848a20b1091441431058848bc001f0004385e00085081e000f8002008484c0400780024e2f00049c5e000f801e042f0007c001613015c0b0e1002d16e021f0004885e000910bc001f003c0c5e000f80020b813805c06e087030200d702080000780022a2f00045059080f8003e000f8003e000f8012109091f8022102f00341c5e006838bc00d071780039080b41c3701081b01122b80872101c840400f00142440f0007c001883c42051080c41e2102883c4205e008838bc011071010831050f80020e28838620e1f00041c40002c2022209a8e6041b8085e061f0005e021f00049c5e000910b420100000003c00178087c00d0717801e022f0004000780021260816061092d4244000024010000000000000000000007801c0cd07092b424228600000000000000000000000000001e00c83848060000000000000000f00341c2263683e8185e0009034247e00090342422a4f00341c22630000000000003c009091010820f00043426030000002181e1ef0b81021a8af040981426050828940a1201000000340c100000000c0a103818200000000000000000000030204000000006819a0e2f0007c001780c0800c63688c108430a09a84c07e06f0001a02601352943423c0421f81bc0011e0981023c51210c2c2602981047826a308f1434411e093144861190930b40d020134340c7020184b424a208c849850420b436084218 else 0xa119092b840bb010800800600500400180806d80852236100928e0289110928de00158085602100025a119092b84097010802400400300400180806d8085e001078002000a800409800808cb840db020800800200400180180986b030402801502600bdc20570305e00178006a0a10000000a000825a12570816e02100480080020030030130d6060bc002f000800000000140010100008130b081b602100a0008080004096b840d70108294202f0c05430150bc002f000bc002f000bc003b0108000002e001b8004000001a060bc002f000800f0008260817030400000000005400204a0028465c206b8104004001001801400c04035818201400a812805ee102b8182f000bc00200000000050004040002012800a025b0823602100a0008080004025001402ae1045c042090b036c040ea1252bc002f000bc003b01080000014c37000dc0037000dc00370008000000e0a13858128e1fa1002e14e0810178405e10178405e101786a1b30b0200129c2002f33c002f000bc002f000bc002e060800000260a10254c3e616e1001796608104481b0581504081b0606c044881120ac100b8202e08005c1385e818e1e05c25c002f000800005c0030200dc0020b8006e00100104017808740c1982848047050900b40c1d030660a12014c1424029820660a12011c1424027030740c1000008210400021082000008420f80020f000400000000000000000000f00120150008465c206d8104012002000800c00c04035818203c00a005405ee102b8182f000bc00350508000001c0c10001b02080f0012015000813001001470822e04100017000dc00370008000000e0813820405e10178405e10178405e101e643402a04c70800bccf000bc002f000bc002f000cc10200000098206608104ee05742006c25c0020b800400d030740c198205c0c198205c0c1982066081982040000000000000001e000f800200681820003c001078002000000000000000000240a10708a044c20a5703041c2281130829400f00041e000f800200000000000d030740c1d030740c1003c00107800201098400781840000000000000000000000000004a88f0ac0c12828488410780020078003e000f8002000000f000400000044208000000a0a1003c001d0307c001b0307c001f00041e00080000000000000000000000000000003c00100000d03041a060c8102282703044c5a0640988858100000f00041e0008000003c001b03040042104000001e000e8183e000800000000000000780020078003e000f8003e00080000000007800209028400000013008000001e0010000001018240608260a1131048020020008010006005003802000c03c4d8183e000b818028015020013002611e017a1c0c1131006002804002500c3420053380012002000800c01021a0201f)) else (if i<29 then (if i<28 then 0x1052e8183e000f8003e000f8003b020d8183b010e8182022b0304045e0008000420f8003a060e8183e000f8003e000810bc001f00044c40003c001021000130084c025050941420000a0a12828620a18828404420800048204a0818820620a12820620e109a8404420a42425080a41c21080842025050c41c31050c41425020a41c31040c41431050e81831028818a2061880852021281052129021240c20000000012021481240c400000903080004810400282862041002204100000482040088284008808400000000441e058288384660591052012061000000000005c0020f00040845020f800204228106e00100000000a0a1002204188104884128284a08100015020c41c39070d41c2d010c41c35050d40c20c81840003414200540435050d408350208000054082000000078002000000001a1210000028484a1212848420a148404a1010441025070841431070940421050c41021050941029030a4092062481a42049030a40c20000a041284940840000a0450111408204808400000008810409080a40c200001101082202100220e1201048029050b4102d01080000001e0008088a021078002041031dc010062003c001000a0e122104000838620a18828488412210521012840620a18820420e128384a0a10441025070c41c25020a42025080841c31040c41021070800000000481240c49030a42029010a40d210248184a04101404250928108a041002204100000000a04128114044088286202100011010800000005030a40c202810400816441440002204104408250208000040b220a1261c0b020283840068285a0210000d020d41c2d020a41c35070b40825050b4142d030a41c29070b414200640c20c818415020d40839030800d0208000000006810400681040d010d4042003408200340820000000000000000000a0a10141c24420800028484a0a100220a122104884100009040941031050c41c25070a4202502080884148404a1018838620e128484a1212838521018828620a12810620a18828520614818450490348409206108a85208148105206148185204903101206108a84050209424228208a040000022a128104545105082d8a0a20440420000050208220418810400883c0b220a30441e059105081100000000816040d050b40c2d040b40839070b4142d020b4142d020b40c39070b408390308019030e404200000068285a04100000681040028385a0e128385a0a16818419030800068285a04100000034082000005050b41025050b41c2d020e40c39030800000000681040d0208000000000000068385a04148385a0a16818520e168385a04168105a041001a02100000034082003408200000000000000000000000001140800115080150808000f000411070f80020000000000000000003604100128 else 0xf00341c5e00c8389e041f0007c001f003c045e000f801e04200000f0004782403f0004205e000840824c1f0007c00100178002002f0004005a060828ac0d907118142605c8084146f020f8002402f00042041300f8003e000f80021080928b40c1f00641c5e006818bc00d071780320e2f00640c5e000f8002082f0007c001f0064042083f00042046040f807c07e08981019826be063f8003e000930bc009071780020f0007c001f000425a1f0004985e000930bc001261780021220968426a1f0004245e000848bc001f00341c59010968b20a1f0005e041f00340c5e000f8003e000848bc019081780032050e8183e00684881e00c828bc01908178003e000e8183a06084d43e000f800a0a2078003e000841c24c209304a0a178107c001f00041c5e000b4243e006838bc0010717801a062f0007c017030030fc00100178002002f0007604107178032102f00141c5e00088143a06083c00108178032102f00341c40d0807c01909178032061041f8002082f0004105e000f8002102f0004205e000f801a062f00640c2083f0004105a060f8002122f00041c52040848bc0010917801a122f00041c5e000910a40a10917800212207801a0e2f0064205e006848bc001f0004145e00c8184107e000820bc00104178002002f0004005e000800bc00100178002122b03041c5b010848b40c10916c0820e278107c0010317801a062f00340c5e000828bc00108178002102f0004105e000f027c03e03d02f01f410119f0323c001f00640c4d097813c05e08f05683a81a026f084f027c05e04f01f81780fa0808af8193e09f00e813c07c05e03f820229e064f8003e000f8032062f00640c5e00081040c7e000818bc001020808fc00101178003e000f8002041031f8002062f00040c5e00081040c7e000818bc00103178003a060818bc001f0007c001f0007c001f0005e001f0007c00178007c001f00040c5a060818ac0c1b0306c0c1b03076021d8087c001020808fc001021780032040810bc001f0004085e0008d8bc001f0007c001f0007c001f0004082023f001c045e000808bc00702178002042f000420bb011481420210518406c0c2080ec085a060810404760608104047e000f8003e007810bc001f0007c001f0007c001f000424c12d178003e000f8003a060f8002042f00064081021780037000f8003e000810bc001d80840856060ec083a060810ac0c10216c083a060810ac0c102178003e000f80020e2f0007c00109178002281071f8003e000898801200f80024c11e183c001b8007c001d808740c1b0307c00178007c001141780022a2f0007c00101178003e000f8002262014143e0008280b061260828920e0421041c2402f00041c2323f0004985e0008384502261052f80000c10708a045422610408484153a060838450226) else (if i<30 then 0x8384404d02100dc05e200a00bc460601789c0c04d138180b627030134402e0178803c02f1001805e201e00b8404a00f0800c02f1001805e2702801805e380980f00463809bc0405e04c2381400c02f1805001e200b8130401400d8802802210050044200a80a0401400b8800150138808280e8042122b0084c0212303640c0408903640c065090a08831070368b4041071580820e203684984d0708128048200f00904e044848806050800000000780040f0008015070c40835020d41c35050d40835070d41035050d40835020800000015090c41020000008828400031f813c07e05f040c2825be0609326204128106a0e1a8286a0e1a81841903082a0a100000014142068384a1010000000000000000000000004420800000340c0660588c0cc0b10460c0b3a06002814c8056030801c09c40263c081063780c8400cc0b1234340c7020435101180b1102320400891d81842608b04810004001002000c00c04a3000400800300400180946000800c0100020030128c009000800c00400602518004001001802000c03c3000c01000600108d00946001001000600100300f0cf01d0340801624001001000600100300f0c003002800800200601e18004001002000c00c04a30130004001001801740c04038024004001001e8180806f017807c07e0504001b0c002000801000600602518004004001802000c04a304c03e000f8002000015090c4082104080260122104050209414200000800200300400180786001001000600100300f0c00200200200796102bc002b03d0309e041f0034085e006838bc0190816819a0e2f0007c00d0713c083e000f801a0e278087c001f0007c00f0116819a0e2d0334244f010e8182f010e819e02298287c001f0034245e006848bc001f003c085e000f8003a060818b40c1f000740c1d030660a1f0005e041f0034085a066810b40cf01168183e0009008000000c6f0203d81980da5780840c607590801980da5d03040da06603a818c93051080b40c13829c0c4e061080b40c703102e001b8006e001000170009414244208015070d40835050d40c25040d41c35070d408350208000c818400002a041054142000000801bc00408838620e104408208840620818820620e10000000220a100221018848621218848620818808620818828620510110220410022021880840004408200818400884c408400001107882840c75070d4043501081a0a168085a0810000003c0020001bc004103083c04130f00f813c060660361fc005051780020031f80bc09e03f0280c160212df0327c001098042601f0005e02100f07c001f0007c001f0007c001f0007c00d091780021300f80020a209807c00108178003e000f8003e00082881e00c838b40c168387c001f0007c0010968421212d178003e00084943e00082880 else 0x5c1d030408004915818203c0248807801e1008c05d2056838e40af0114815c0c0631c815c0c09b7809005cd09138180b8f02181983e0650489c021f0318145205780880cc1044b8044e050360805d2056848e40af0214815c0c0631c815c0c0711c815c0c08c78111c0817008424c107818c0a200025a10930424c10930421210000d07082c041084840cc101734244003a840cc10022c3e0611109c041260838c0ccd071000cc100110782002033141c405c08199a0e202e040c0603108005c0841c21090b424202e6838805cd09100b9a0e2603018841090bc082f010801805e270301704c060310b80d81e1781b03c2703026ce0237030170e04370301c4460601789c0c08c7810cc0c02f7808fc0c02e170181042f0302084126096801805c400300bc40060178980c0621101805e200201005c0603f8b404006017841c9a0200300b82281072d81400c02e0899000c02f1680400c02e1e81405c10708c9180c05415818204a00f09c0c170306c0c178148056023781409c03438140068403c0118ac0c170306a0ea0615c054087041bc0a06001a1810007e280c006859090c819a1227814821610378140c0034302000bc501800d080080382681865072848ae027041541da0e70419c08e02203600b858063816024a1240366819e0431120078404a00f0808001e1000e06080f0046278080f00603902341452066838a408b0414811608281a80a8560601e00b8600978080f005e49022c10503500b0809601611c102038080f003c31120078404a00f0805c055100f005c2025007859046838a4089041481120820250078404a00f0807802e1012803c200300bc4d070812804626810402802f1340808002f1812803c20250078403c0170809401e1001805e2001a0a101e00bc4d050b4102d050805805e2681005805e301180784c0602a0980c054178180942603012844060178980c04b10078046200f00bc401a0178806e01e1001805e270301344e0602d8800c02f1341c2d0101e00bc602f0170806e01e1301400c02f1801805e26)))))
def combl10 : Packing := (2559,5,8,8,4,16,0,combd10)
def combd11 (i : Nat) : Nat := (if i<18 then (if i<9 then (if i<4 then (if i<2 then (if i<1 then 0x6813280377d33340c1401bbe999a04ca00ddf35133265006df9a59dd328036fcd34ee99401b7e692774ca00dbf3433ba65006ef9a19998280377cd3cccc1401bbe6926660a00ddf34b33305006ef9a19993280377cd3ccc99401bbe692664ca00ddf34b33265007d7a559dd32803f7908cccc1401fec912114ca00fde42333265007fb24484582803f75114ccc1401e7ea22774ca00fdd44533265007dda339dd32803f6d19ccc99401fb68ce6660a00ff548911305007faa4488932803d7d444cc99401eee912884ca00ddf4cd552650047fc9b6a1328027fc4db50994013fe5aca94ca008ff936d3265004ff89b699328023fe8d952994013fe46ca94ca00cefcaa54a65006f7a552a5328036fd3b952994013fe5aca960a008ff936d3305004ff89b699828023fe8d952c14013fe46ca960a008ff936d0b05004ff89b685828031fec0952c14019fe42ca960a00cff24054b050067f6112a5828033ef19952c14019fb888a960a00cdfccc54b05006bf9812a5828037f908952c1401bf68cca960a00dfd44454b05006efa662a5828027fc55c2299401bfc2ae114ca008ff936d0a65004ff89b685328027fcbd952994013fe26da74ca008ffab654a65004ff95b2a5328023fe4db4a994013fe26da54ca00cfba6254a650067f6112a5328031ff44152994019bf998a94ca00dfb26254a65006ff2112a5328037f51115299401bf68cca94ca00d7f51054a65006efa662a5328027fc55c22c1401bfc2ae1160a009ff15744265006bf8aba21328027fc55c66c1401bf62ae3360a009ff2d755265004ff97baa9328027fcc5d54994013fe46eaa4ca00dfe42355265006fd973aa9328037ec98d5499401bfa50aaa4ca00dfd30555265006bfa88aa9328037bd2ad5499401b7e9deaa4ca00df748955265006fda33aa9328037f511554994013fe46eaa60a00dfb46755305006fba44aa982802dfd5db02c14013fe5aeaa60a009ff27755305006fe962aa9828035fcc0d54c1401bfa4caaa60a00bfb57698a65006ff211aa98280377d33554c1401bfa88aaa60a009ff576d4265004ffabb685328023fe4dd54c14013fe26eaa60a008ff93755265004ffabb695328027fd5db42c14013fe26eaa4ca00bfd576b1305005fdabb5cd328027fd5db4c994013feaeda74ca009ff576d3305004ff8ab58d8280377c35b42c1401b7e1eda54ca00f5f0d6c0b05004ff8ab5c5828027fc55b08994013fe2ad714ca009ff156c3a65004ff8ab59532802fec1db48c1401ff20ed824ca00dfb34651b05007fc82b4c532803df45430499401afe6a0a84ca00ffa14298a65006ff1a128532803df850b02c1401bfc684a160a00f7d056c0b05006f79a529532803df845c22c1401efa0ae884ca00ffa07708a65007fc82b8cd828023dea5952c14013ee52ca960a00 else 0x1bf64c5a04ca00dfb262d3265005fd93b21532802fec9d902994017f64ec514ca00bfb27648a65006fe982695328037f4c134c994017fa56d6260a00d7f302d0305006bf98169982802dfcc5862c14017fa4ac854ca00bfd25649b05005fe92b26132802dfcc5922c1401bfa589a160a00bfd25618b05005fe92b20532802ff4958a2c1401bbe58da660a00ddf2cad3305004ff98b681328027fcb5b40994013fe5ada060a009ff236d0305004ff91b681328027fcbdb40994013fe56da04ca009ff57654b05004ffabb2a5328027fcbdb4cc14013fe5ada74ca009ff316d3a65004ff98b695328027fcd5b04994013fe5ada54ca009ff2d6d0a65005df97b21532802efcbd902994013fe5eda160a009ff2b6d0b05004ff9ab24d828027fcb5b42c14013fe6ad8160a009ff35618b05004ff9ab145828027fcd5922c14017be5aca360a00bbf2f650b05004ff91b69d328027fc8db4a994013fe6ad214ca009ff35640a65004ff9ab261328027fcd5922994013fe5eda54ca009ff356a9265004ff9ab215328027fcd58a2994013fe6ac954ca00bdf2d642a65004ff8ab601328027fc9d952c14013fe2ad3160a009ff156c2a65004ff98b2a5328027fc55b02994013fe2ad5160a009ff156a8a65007fe16284582803ff099422c1401ff850a114ca00ffc2a508b05007bf18384582803df908b02c1401efc61e1160a00fed2852aa65007fd2114c532803fe8b9c2299401bde955a54ca00def34d2aa65006f79a4955328037f8d1c22c1401bfc845a160a00dfe34908b05006ff211681328037f8d342299401bfc845a14ca00dfe34f08a65006ff1a4845328037f8d2c22c1401bfc845a060a00dfe34f08b05006ff1a684582803ff108c44c1401ede956884ca00ffc42311265007f725584582803fe4c146699401ef66063360a00ff92c519b05006fda33681328037ecd446699401bf669a334ca00dfb34319a65006fd9a78cd328037ecd2c6699401bf68cda060a00dfb34319b05006fd9a68cd828027fcadd5499401efa60e2260a00f7d28544265007be98188982803dec98d1099401ef65ce884ca00ff926311265006fea22681828037f51134099401bfa68e2260a00dfd34b11265006fe9a6889328037f4d244499401bfa686224ca00dfd34b11305006fe9a6889828037f4d2444c1401bfa6862260a00d7f34344265006bf9a4a21328035fcd3d1099401afe69a884ca00d7f34b44265007bea8888982803df51151099401fda9562260a00fed4ab11265007fd2118cd32803fe519c4499401ff28ce2260a00f7b46744265007bf211a2132803fe908c66c1401fba60a664ca00fdd28533265007ee95299982803f6c98ccc99401fb65ce664ca00fbb2633ba65007af98399982803d7cc0cccc1401ebe61e6660a00fbd2853ba65006dfa77) else (if i<3 then 0x6254b05007fe85160932803ff428a8499401bfe145a060a00dff0a2d0265006ff8516a1328037fc28b48c1401bfe145a44ca00ffb0a319b05007fd8518cd32803ff418c44c1401ffa146224ca00ffd0a311305007bf851a21328037fc28d54c1401bfe146aa4ca00cff8a254b05006ff8512a5828037fc2895299401bfe0c6aa60a00ffb26249b05007bf48b84582803ff449ac4c1401efe24d8160a00dff126d0b05006ff89369982803ff849c22c1401ffc22e114ca00fdf12733305007fe89388982803dfc0dd1099401bfe24eaa60a00dff07654b05007bf98526132803dfcc093099401efb0ae884ca00ffa87708a65007fd8985cd32803fec4c26299401bfe261a74ca00dff130d2a65006ff89868532803ff44c44499401ffc0ee1160a00ffe13108a65007ff05b84582803fbc0dcaa99401ffc16e114ca00fbf1313ba65007fd8988cd32803fec0dc66c1401bfe262aa4ca00dff0b755265007ff15124532803ff8a8922c1401fde544954ca00ff985719b05007fe89558982803ff44ab0499401ff6245734ca00ffb12a98a65007fe89160932803dfc4ab02c1401bfe245a74ca00dff12ad3305006ff895699328037fc48b5099401bfe245a54ca00dff12ad0b05006ff89568532803fbc45caa99401ffc2561160a00ffe12b08a65007bf891a2132803ff44ac44c1401ffa256224ca00ffb12319a65007fd8918cd82803fec4ac6699401bfe256aa4ca00ffd12311265007fe89188982803dfc4ad1099401efe16e884ca00dff12355305006ff891aa932803efc48cee99401fbe2566660a00fdf12b33265006ff81b2a5828037fc45d5499401bfe06eaa4ca00dff03755305006ff83baa982803f5d224ccc1401fae912664ca00fb74893ba65007cfa7799982803e7d3bccc994015ef52ca960a008ffa7654b050047fd8b2a5328023ff5d952c14017ee52ca360a00bf729654b05005fb94b28582802fdca5902994017ee52c984ca00bf729642a650067bd4b2a5828037dca5952c1401f9e956664ca00fbe4233ba65007e7a5599982803fcd222e699401fe6911314ca00f77488c0b05007faa4460932803fd5222c4c1401bee911a84ca00df7488d3305006fba44685828037dd2234299401bee911a74ca00df7488d3265006fba4469532803fcd22466c1401ff4605314ca00f7e2c2c0b05007bf131605828037f898b42c14017fc46ca360a00ffa24298a65007fd1414c532803df8a8b02c14017fc46c854ca00f7d30eb1305007ee96358982803f74b0ac4c1401fba5d96260a00fdd2cab1305007be98360932803df4c1ac4c1401efa4c98160a00f7d2a4c0b05007be98158982803fe4b9b0499401ff25cd424ca00fbb2e6b8265007dd9875cd32803eecba2e6994017f65ed314ca00dfb2e6d2a65007fc93160932803fe498a84994 else 0x2802ffcbd862c14017fe52c5160a00bff2f64c265005ff96b24d82802ffcbd922c14017fe5ec914ca00bff2d64aa65005ff8ab58d828027fe55ac6c1401fbe1ada160a00ddf8d6d0b05007df87b695328036fe3db4a99401ebf1ad8160a00fdf0d6c0a65005ff8ab5c5828027fe55ae2c14013ff2ad714ca009ff956c3a65005ff8ab505828027fe55aca994015ff26d874ca00bff136c3a65005ff89b58932802ffc4dac4c14017fe26d6360a00bff136b1a650057fc9b59532802ffc4dae2c14017fe26d714ca00bff136b2a65006ff83b681828037fc0db40c1401bfe0eda160a00dff116d2a65006ff81b68132803fec1db48c1401bfe0eda660a00ffb34651b05007fd93228d82803fec51a60c1401ff30ed824ca00dfbb4651b05007fe82b4c532803fe615a6299401ffa28d6260a00f7f146c0b05006ff8a3681828037fcd0946c1401bfe698a360a00dff15251b05007ff0a384582803f7c51cccc1401ffa28e2260a00dff55451b05006ff85b699828037fc45b4299401bfe06da84ca00dff116d0265006ff81b69532803df65430499401aff6a0a84ca00ffa94298a65006ff5a128532803fec5426299401bfe694a84ca00dff34254265006ff8a868132803ff85442299401ffa285824ca00dff142d0265006ff9a8285328037fcd294299401fde286554ca00f7f14344265006ff85b681328037fc2db42c1401ffa0ad534ca00f7e942c0b05006ff5a128582803ff8d0942c1401ffc484a160a00ffe30250b05007fb8a191182803fec45a6299401ffa2956260a00ffd0b6c1265007fe81b60932803dfc52b02c1401bfe285a060a00dff34e50b05006ff9a3285828037fcd2942c1401bfe690a160a00dff14650b05007ff0a584582803ff452c44c1401ff62863360a00ffd14311305006ffaaa28582803f7c52cccc1401bfe2a4a160a00f7d856c0b05007bf83b60582803dfc2db02c1401ffa0ed6260a00ff710b22265007fe88550932803fec42a6299401bfe215a04ca00dff10ad0a65006ff88569132803ff842c2299401ffa216224ca00ffb10b19a65006ff8852a5328037fc42d5499401bfe16da14ca00ffb0b698a65006ff85b699328037bed294a99401fbe296664ca00ffb14a98a65007fe8a5609328037fcd414a99401bfe295a04ca00dff34252a65006ff9a629532803ff852c2299401efe296884ca00ffd0b6b1305007fb88191132803fec40ae699401ffa205424ca00dff102d0265006ff88169d328037fc40b4a99401bfe205a44ca00fef1032aa65007fd8818cd32803ff440c4499401f7e206774ca00dff10254a65006ff881aa932803f7c29cccc1401fee1464460a00ff70a322265007fe85358982803dfc29b02c1401bfe0c5a060a00dff0a6d0b05006ff85369982803ff429c44c1401ffc14e1160a00dff0)) else (if i<6 then (if i<5 then 0xe58da14ca00dff2c6d0265006ff96369532803ff8b9c22c1401ffc5ce114ca00ffe30f08a65007f796295532803ff8c3c22c14019ff58ca960a00dff2c654b05006ff9632a532803ff4c230499401efe5098160a00ffb308b9a65007fd9844c532803feca126299401bfe611a74ca00dff284d3265006ff984695328037fca134299401bfe611a14ca00dff284d2a65006ff984699328037fca135099401bfe509a660a00dff284d0b05006ff98468582803ff4c244499401efe50a884ca00f7f2c544265007fe984889828037fca1554c1401ffc58e1160a00ffe30908a65007f794295532803ff8b1c2299401ffc6121160a00dff2c555305007fd9654c532803fecb2ae699401ff65c5314ca00ffd2cac1265007fe96550932803dfcb8b02c1401efe5958160a00ffd2e2a1265007fe97160932803ff4b8ac4c1401bfe5c5a460a00dff2e2d2265006ff971681828037fcb8b4099401bfe595a160a00dff2e2d2a65006ff9716a1328037fcb8b4cc1401bfe5c5a160a00dff2e2d3265006ff971685328037fcb2b4899401bfe595a04ca00dff2cad0a65006ff96569d328037fcb2b4a99401ff65c63360a00ffb2e319a65007fd9878cd32803fecb146699401ff658a3360a00ffb2cb19a65007fe96388982803ff4b2c44c1401efe5c6884ca00f7f2e744265007fe96388932803ff4b2c4499401bfe596aa4ca00ffe2cb08b05007f797195532803ff8a142299401ffc596114ca00ffe28508b05006ff962aa9328037fcb1d54994019ff5c4a960a00dff2e254b05006ff9712a5328033feb295299401bfe594a94ca00dff30f55265007fb98791132803fdcb148899401fee58a4460a00fdf2e733305007ef97399932803efcb1cee99401f7e612774ca00fdf28533265007ef94299982803fdcb8c88c1401fee5c6444ca00ff72cb22265007fe95458982803ff4aa30499401efe5058160a00ffb282b9a65007fd9544c532803fecaa2e699401ff6505314ca00ffd282c1265007bf95460582803ff4a0ac4c1401bfe505a74ca00dff2a8d3305006ff954699328037fca0b5099401bfe505a54ca00dff282d3265006ff941685328037fcaa342c1401bfe505a660a00dff282d0b05006ff954685328037fcaa34e99401bfe551a54ca00fef2832aa65007ff15484582803ff8b142299401ffc552114ca00ffe2c508b05007bf941a2132803ff4aa444c1401efe58e884ca00ffd2a911265007fd9418cd82803feca1466c1401bfe552aa4ca00ffd28311265007fe94188982803dfcaa51099401efe596884ca00dff28355305006ff941aa932803efca0cee99401fbe5526660a00fdf2a933265006ff984aa9328037fcb8d5499401bfe5c6aa60a00dff2c755305005ff96b28d82802ffcbd942c14017fe52ca160a00bff2d652a65005ff97b2053 else 0xa65007fb97691182803fdcbb48899401ffa5d16260a00ffd2e8c1265007bf96460582803fecb22e699401ff65d1314ca00ffb2c898a65007fe96460932803dfcba302c1401bfe591a74ca00dff2e8d3305006ff974699328037fcb235099401bfe591a54ca00dff2c8d0a65006ff974685828037fcb2342c1401bfe5d1a14ca00dff2e8d2a65007f796495532803ff8ba422c1401ffc5da114ca00ffe2e908a65007ff17684582803dfcb251099401ff65923360a00ffd2c911265007fe96488982803dfcba51099401efe5da884ca00fbf2c93ba65007ef97499982803f7cba4cc99401bfe592aa4ca00dff2ed55265006ff976aa9828037fcb2554c1401ffa50d6260a00f7f286c0b05006ff943685828037fca1b4cc1401ffa619424ca00ffb30cb9a65007fd9864c5328037fcc334e99401bfe619a54ca00dff30cd0265006ff986685328037fcc334899401ffa61a224ca00ffe28708b05007ff186845328033fec315299401bfe618a94ca00ff730d22265007ef94399982803efcc34ee99401fee5864460a00ff72c322265007fb97591132803ff4baac4c1401ffa5d5824ca00ffd2eaa1265007fd9615cd32803fecbaa6299401ffa585824ca00f7f2eac0b05007fe961509328037fcb0b4099401bfe585a060a00dff2ead0265006ff96169d328037fcbab4cc1401bfe5d5a64ca00dff2c2d4265006ff961695328037fcb0b4899401bfe5d5a160a00dff2c2d2305006ff975685328037fcbab4899401fde586554ca00ffe2eb08b05007ff17584532803ff4a1c44c1401efe586884ca00ffb30d19a65007fd9618cd32803fecb0c66c1401ff65d6334ca00dff2eb55265007fe96188932803ff4b0c44c1401efe5d6884ca00fbf2c33ba65007ef97599982803f7cbaccc994019ff584a94ca00dff2c254a650067fd612a5828037fcb0952c1401bfe5d4a94ca00dff30d55265006ff961aa9328037fcb0d54c1401bfe50eaa60a00fdf30f33265007fb96391182803f7cc24cc99401fbe5c66660a00fdf2e333265007df9659dd32803f7ca0ccc99401fbe5066660a00fbf2a93ba65007fe98750932803dfcb1302c1401ffa61d824ca00ffb30e98a65007fd9624c5328037fcc3b4a99401bfe589a14ca00dff2c4d0b05006ff987691328037fcb134899401bfe589a460a00dff30ed0a65006ff987681328037fcc3b4c99401bfe589a84ca00dff2c4d2a65006ff962681328037fcc3b42c1401bfe589a060a00dff30e54a65006ff9622a5328033fec3952c1401bfe588a960a00f7f2e6c0b05007fe96360932803ff4b9ac4c1401efe58d8160a00ffd2e6c1265006ff973699828037fcb9b4c99401bfe58da160a00dff2c6d0305006ff973685828037fcb1b5099401bfe5cda54ca00dff2e6d0265006ff973685328037fcb1b4e99401bf) else (if i<7 then 0x7fcb055499401bfe5c2aa4ca00dff22155265006fed82aa9328037fcc2d5499401bfe54eaa4ca00dff2a355265006ff983aa9328037fcc0d5499401bfe4c6aa4ca00f7f55544265006bfe88aa9328037fd4455499401fdeaaa554ca00dff4ab55265006dfe77aa932802ffc4dcaa994017fe26e1160a00efe93708a65005ff89b84532803bfa4dc22c1401fde26e554ca00ffe13708a65007ff09b845828037ef19d5499401bfb88aaa4ca00bff23755305004ffd1baa982802ffd5daa2994017feaed5160a00ffb55519b05006fde33aa982803fdd55488c14015ff26e3360a00f7f576c0b05005ffabb60582802ffd5daa4994016ffaed8160a00bff576c0a65005ff89b8cd82803bee4dc66c1401ff626e3360a00bff29755305005ff96baa9828027feb5d54c14017fe4eeaa60a009ffa77553050057fc9ba2132803ff5552c4c1401efeaa98160a00ffd576c1265006ffa33aa9828037fd55340c1401bfe686aa60a00dff34955305006ff9a6aa9828037fcd1d54c1400ffeaeeaa60a00dff24355305006ff920aa9828037fcc0d54c1401bfe4caaa60a00dff2a355305006ff910aa9828037fc85d54c1401bfe582aa60a00dff26155305006fed62aa9828035fec0d54c1401bfb4caaa60a00dff23755305006ff931aa9828037fc54d54c1401ff6aed314ca00bff576a9a65005ffabb4c532802fef5da62994017feaed3160a00ffe55508b05006ffa11aa9828037fb08d54c1401fbeaaa6660a00ddfccd55305005ff89ba21328039fe4dd1099401ffaaaa2260a00dfdc4555305007bf89ba21328037fca5d54c1401bfe5aeaa60a00dff27755305006ffabb6a132802ffd5db46c14017feaeda84ca009ffd76d4265006ffabb68532802ffd5db42994013ffaeda14ca00aff93755305006ffabb68182802ffc4dd54c14019ff26eaa60a00dff137553050057fc9baa9328037fd5db4a994017feaeda54ca009ffd76d2a65006ffabb68582802ffd5db42c14013ffaeda160a00cff93755265006ffabb68132802ffc4dd5499401bfe26eaa4ca00bff576a0b05005ffabb58982802ffd5dac4994017feaed874ca00bfdd76b1305005ffabb58d32802fef5dae6994017feaed6360a00bff576a1305005ffabb699328027ff5db4c994013ffaeda74ca00bff576d2305005ffabb699828027ff5db4cc14017fe5ad874ca00bff296b1b05005ff96b5c582802ffcb5ae2994017fe5ed654ca00bff2d6a0b05007f797495532803ff8b242299401ffc5921160a00ffb2ec98a65007bf97660582803ff4bb28499401ffa5d9824ca00dff2ecd2305006ff976681828037fcbb35099401bfe5d9a160a00dff2ecd2265006ff976681328037fcbb34299401bfe5d9a54ca00ffb2ed19b05007fd9768cd328033febb152c1401bfe5d8a960a00dff2ec54 else (if i<8 then 0xa94ca00cff936d32650057fc9b699328037fc4db4c994017fe26da64ca00bff23654a65007f78ab95532802ffcb5952c1401bfe26da660a00bff136d33050057fd1b2a582802ffc8d952c14019ff26da160a00aff936d0b05006ff89b68582802ffc4db42c1401cff604a960a00e7fb0e54b050067fda72a5828033fed0952c14019ff4c4a960a00cffa4254b050067fd812a5828033fea8952c1401dfd844a960a00cffc2254b050075fe772a582803ff44db0499401efe2a58160a00ffd152b1305006ffabb2a5828037fcd1952c1401bfe698a960a00dff34254b05006ff9322a5828037fc9d952c1401bfe4c4a960a00dff24254b05006ff9812a5828037fca8952c1401ffc2a61160a00dff42254b05007fd8a98cd828037fd19952c1401ffa2a62260a00fdf153333050067fd7b2a5828037fcb5952c14019ff46ca960a00dff23654b05007fe89b58982802ffcad93099401ffc2ae114ca00dff136d0a65005ff89b68532802ffcad952994019ff26da54ca00aff936d2a65006ff89b69532802ffc4db4a994019ff954a94ca00cffb0254a650067fd852a5328033fea895299401ffa2a5824ca00ffb15298a65006ffa552a5328037fcd315299401bfe5aca94ca00dff35054a65006ff9832a5328037fcc115299401bfe604a94ca00dff31654a65006ff9852a5328037fcd095299401bfe694a94ca00dff26254a65006ff9532a5328037fc9095299401bfe548a94ca00dff23654a65006ff9512a532803ff854c2299401bfe844a94ca00dff51054a65007bf8a9a2132803f7c54ccc99401bfe56ca94ca00bff23649b050057fc9b4c582802bfe4daa6994017fe2ae1160a009ff95708b05007fd89b4c532802ffc4da62994017fe26d3160a00bff136a9a65007ff0ab845828037fa55c22c14013ff2ae114ca00aff936c2a65004ffcaba21328037fa55c22994017fe26d854ca00bff13690b05005ff89b485328035fe55d1099401efe2ae884ca00bff2364c2650057fc9b60532803dfc4db02c14017fe26d814ca00bff136c0b05005ff89b54932802ffc8d92a994017fe56c9160a00bff2b648a650057fc9b54582802bfe4daa2994013ff2ae3360a00bff15719b05005ff89b54582802ffc4daa299401bf72ae3360a00ffb15719b05004ffd6baa9328027febdd54994013ff62eaa4ca009ffa37552650057fc9b95532802bfe4dc22994015ff26e1160a00bff57690b05005ffabb48532802ffd5db0a99401ffcaaa114ca00dfec2355265006fdd73aa932803fed5526299401bf74c6aa4ca00ffd554c1265006ffa11aa9328037fd5534099401bfe482aa4ca00dff34b55265006ff952aa9328037fcd455499401bfe60aaa4ca00dff34d55265006ff9a1aa9328037fc90d5499401bfe542aa4ca00dff30155265006ff930aa932803 else 0x6bfda7a21328035fed351099401bfea21a54ca00d7fb4b44265007bfa55a2132803dfd4430899401efea21804ca00f7f30344265007bf9a8a2132803ff4c1c44c1401ffa60e224ca00f7f510c3a65007bf985a2132803dfcd251099401ffa616224ca00f7f34144265007fe98588982803dfc9851099401efe5c2884ca00f7f2c144265007bf950a2132803dfcd0d1099401efe486884ca00f7f26344265007bf9a7a2132803dfcd351099401efe696884ca00ffd30311265007fe98188982803dfca951099401ffa4c62260a00ffd26311265007fe95188932803ff4a8c44c1401efe546884ca00f7f2a744265007bee8888982803ff54444499401efb88a884ca00ff9c6711265007fce3388982803fb72ac44c1401ff6956334ca00ffb42319a65007bde33a2132803fed4446699401ffa9562260a00ffd4ab11265007fd6118cd32803ff519c44c1401ffca22114ca00f7ec2344265007bfa11a2132803ff919c22c1401ff68463360a00ffac2319b05007eed8299932803f76a94ccc1401fb74c6664ca00fdbae733265007ddd319dd32803d7ec1cccc1401ebf6066660a00f5fb0f33305006efda8999328036fed2cee99401b7f69a774ca00dbfb433ba65007dfa119dd32803efcd04ee99401f7e4c2774ca00fbf3013ba65007df9509dd32803efcb04ee99401f7e442774ca00fbf3513ba65007df9a59dd32803efcd34ee99401f7e686774ca00ddfb4333305006efda79998280377ed2cccc1401fbe9566660a00fdf34133305007ef93099982803f7c904ccc1401fbe4426660a00fdf2e133305007ef95099982803f7cd1cccc1401fbe6866660a00fdf34f33305007ef9a499982803f7cd2cccc1401bbf686664ca00ddfb4f33265006efda599932803f7d2accc99401fbe602664ca00fdf34133265007ef93099932803f7c904cc99401fbe442664ca00fdf2e133265007ef95099932803f7cd44cc99401fbe60e664ca00fdf30533265007ef98199932803f7cc2ccc99401fbe686664ca00fdf34f33265007ef9a499932803f7cd2ccc99401f9f9566660a00fbf2a73ba65007ef93199982803f7c98ccc99401f7e4c6774ca00fdf2a733305007ef95399932803efb08cee99401f7e616774ca00fdf24333305007ef92199932803efcc0cee99401fbe54a6660a00fdf2a533265007df9519dd32803f7ca8cccc1401fbe546664ca00ff74ab22265007ef61199982803fdd08c8899401fbd846664ca00ff742322305007eee2299982803f77114cc99401f7ea22774ca00f3fd113ba65007dde339dd32803f6f19ccc99401fbe8ce6660a00fdbc6733305007afe8899932803fdd4448899401fbeaaa664ca00ddfccd55265005ffabb59532802ffd5dae2994017feaed7160a00dff136d4265005ff89b68d82802ffc4db50994017fe5ac)))) else (if i<13 then (if i<11 then (if i<10 then 0x9422c1401ffc6961160a00ffe30b08b05007ff1a084582803ff8c0422c1401ffc69e1160a00ffe34d08b05007f798595532803ff890c22c1401ffc542114ca00ffe24308a65007ff15084582803fbcc0caa99401ffc54a114ca00ffe2a508b05007f7a5559532803ff908ae2c1401ffc5c2114ca00ffe422b8a65007ff17084582803fbd2aaa899401ffc8454160a00ffe2c108a65007ff21150532803ff8b0422c1401fde546554ca00ffe2a308b05007ff12084532803ff8a8c2299401ffc4821160a00ffd422c1265007fea1150932803dfd2ab02c1401ff6845734ca00f7ec22c0b05007fda554c532803dfac3c22c1401ffa955824ca00ffd4aab1305007fea5550932803feb08a6299401ff55ce114ca00dff4aad0265006ffa11681828037fb08b4299401bfe845a04ca00dfec22d0b05006ffa116a1328037fd2ab4c99401bfe955a44ca00dff4aad0a65006ffa55699828037fd08b48c1401bfe955a160a00dfeb4f08a65006ff5a6845328037fd08b4e99401bfe845a44ca00dff422d2a65006ff5a7845828037fad3422c1401ff98462260a00ffcc2311265007f7a1195532803ff92ac2299401ffc9561160a00ff9b0519a65007bdd818cd82803fe6b1466c1401ff6682334ca00ffb22119a65007fd9508cd32803fecd346699401ff66a2334ca00ffb34319a65007fd9a58cd32803fecb046699401ff65c2334ca00ffb30119a65007fd9208cd32803dfd19b02c1401ffa8cd6260a00dff466d0305006fdda18cd328037eed2c6699401bf769a334ca00dfbb5119a65006fdda78cd328037fd19b42c1401bf76863360a00ffb30b19a65007fd9218cd32803fecc0c6699401ff654a334ca00dff466d3305006fdda68cd82803fed19a60c1401ff64c63360a00ffb34719b05007fda3358d82803fecc146699401ff65463360a00ffb2a319a65007fd9a08cd82803fecb0466c1401ff64823360a00ffb34319b05007fd9218cd82803fecc0c66c1401ff669a3360a00ffb34919b05004ffd5baa932803df6c1c44c1401ffaa21424ca00f7db0311305007bdd31a2132803fed4426299401ef75ce884ca00ffb510b9a65007fcd3188932803ff508c4499401ffa682224ca00ffd2a111265007fe9a888932803ff4d2c4499401ffa69a224ca00ffd34311265007fea1188982803ff4d0444c1401ffa6022260a00ffd30111265007fe9a388982803ff4d2c44c1401ffa69a2260a00ffd34911305007fe9a188982803ff498444c1401ffa4c2224ca00ffd2c111305007fe96088932803ff488444c1401ffa442224ca00dff510d0265006feda5889328037f6d444499401bfb69a2260a00dfdb4311305006feda6889328037f6d0c4499401bfea21a14ca00dff510d2265007f765584582803ff4a9c4499401ffa54e2260a00dff510d3a650 else 0xa00dff2a6d0a65006ff95369d328037fca9b4a994017fe4eca160a00bff27642a65005ff93b20532802ffc9d8a2c14017fe4ec514ca00bff27648a65005ff93b24582802ffc9d92a994017fe46ca360a009ff95698b05005ff8ab4c5828037fc55a62c14017fe62d654ca00bff256a0b05005ff98b54532802ffc95aa2c14017fe4ad514ca00ffb30ab9a65007fd9214c532803fecc2a6299401ffa615824ca00f7f242c0b05007fe985509328037fcc2b4099401bfe485a060a00dff242d0265006ff98569d328037fc90b4cc1401bfe485a64ca00dff356c2a65006ff9216a1328037fcc2b4a99401bfe615a64ca00dff30ad2265006ff985685328037fc90b42c1401bfe485a460a00dff30ad0b05006ff921685328037fc90b4899401bfe485a54ca00bff31652a65005ff95b2a132802ffc95902994017fe4ac3160a00bff31654a65005ff92b26132802ffc95926c14017fe62c954ca00bff25648b05005ff92b24532802ffcc5ac2994017fe62d4160a00ffb302b9a65007fd9524c532803fecc0a6299401ffa605824ca00f7f2a4c0b05007fe981509328037fcc0b4099401bfe605a060a00dff2a4d0265006ff98169d328037fca934cc1401bfe549a64ca00dff356c0a65006ff9816a1328037fcc0b4a99401bfe605a44ca00dff302d0a65006ff952685828037fcc0b48c1401bfe605a160a00dff2a4d0a65006ff952691328037fca934a994017fe62ca14ca00bff25642a65005ff98b0c582802ffcc58a2994017fe4ac5160a00bff25628a65005ff98b24532802ffcc5922c14017fe4ac954ca00bff23654265004ffcab60532802ffcbda82c14017fe46d654ca00bff2b6b8b05005ff95b5c532802ffcada82c1401ff6545734ca00ffb2a298a65007fe95160932803dfca8b02c1401ffa5456260a00ffd2a2a1265006ff951681828037fca8b4099401bfe545a84ca00dff2a2d3265006ff9ab545828037fca8b4cc1401bfe545a460a00dff2a2d0b05006ff9ab545328037fca8b4299401bfe545a74ca00dff2a2d2265006ff95169532802ffc8d94a994017fe56ca160a00bff156a8b05005ff95b20532802ffcad942994017fe56c3160a00bff23642a65007fe56284582803ff299422c1401ff954a1160a00fef4aaa8265007f79a595532803fbcd34aa99401fde692554ca00fef3432aa65007f795295532803ff8d042299401ffc4c2114ca00ffe42288265007ff1a684532803ff8d442299401ffc60e114ca00ffe30308a65007ff18584532803ff8d0c2299401ffc69e114ca00ffe34908a65007ff1a584532803fbca9caa99401ffc602114ca00ffe26308a65007ff13184582803ff8d0c22c1401ffc6061160a00ffe42288305007ff1a484582803ff8d1c22c1401ffc60e1160a00ffe2a708b05007ff13084582803ff89) else (if i<12 then 0x96b685328037fcd334299401bfe62da14ca00dff350d0a65006ff982685328037fcbdb4299401bfe52da14ca00dff2b6d0a65004ffdab205328027febdb4a99401bfe69d604ca00dff34ec0265006ff9a7681328037fcd3a6099401bfe69d104ca00dff34ea8265006ff9a669d328037fcd434e99401bfe685a74ca00dff34cd2265006ff9a8691328037fcc134899401bfe685a44ca00dff34ab0265006ff9a5601328037fc85b4a99401bfe695a04ca00dff34a98265006ff9a5481328037fcd2a2099401bfe695704ca00dff34aa8265004ffdab549328037fcb5b4a99401bfe699a54ca00dff316d2a65006ff9a8695328037fcc134a99401bfe46da54ca00dff342d2a65006ff97b695328037fcd3b4a99401bfe52da54ca00dff348d2a65004ffdab215328027fed58a299401ffa60d824ca00f7f302c0265007bf98161932803dfc99302c1401efe615804ca00f7f30ac3a65007ef96358132803f7cc32c699401fbe589634ca00fdf2c2b0265007ef96158932803f7cb2ac099401fbe619654ca00fdf2c4b2a65007ef97659532802f7eb590a994017fe5ad804ca00bff2d6d0265005ff96b4c132802ffcb5a40994017fe5ad104ca00bff2d6b8265005ff96b54132802ffcc5b4099401bfe60da04ca00dff264d0305005ff98b44132802ffcc5ae0994017fe62d504ca00bff35688265005ff9ab5c132802ffcd5aa0994017fe42ca84ca00bff27688265005ff93b5c132802ffc9daa0994017fe4ad104ca00bff256a8265005ff91b5c132802ffc8daa0994017fe42c814ca00bff21650a65005ff97b54132802ffc8590a994017fe42ca54ca00bff21628a65005ff9ab619328037fcc1b4e99401bfe4c9a660a00bff356b0a65005ff9ab5d932802ffcd5aca994017fe5ed634ca00bff236b1265005ff92b59532802ffcd5b02994017fe6ad874ca00bff356c2a65003ff9326a1328037fcc1b4a99401bfe60da64ca00dff306d0a65006ff932685828037fcc1b42c14017fe62d714ca00bff2b6c3a65005ff9ab5c532802ffcd5aa299400ffe4c9a14ca00bff35640a65005ff9ab26132802ffcd5922994017fe6ad754ca007ff264d2a65005ff9ab21532802ffcd58a2994017fe6ac954ca00bff276b2a65005ff93b5c582802ffc9dae2994017fe4ed5160a00bff276a8a65007bf98b4c582803ff4a9b0499401efe4c58160a00ffd2a6b1305005ff93b2a582802ffc9d930994017fe46d634ca00bff236b1b05005ff95b5cd32802ffc9da82c1401ffa4c5824ca00f7f2a6c0b05007fe931589828037fc98b4099401bfe4c5a060a00dff2a6d0265006ff93169d328037fca9b4cc1401bfe54da64ca00dff35698b05006ff9316a1328037fc98b4a99401bfe4c5a64ca00dff262d0a65006ff953685828037fc98b4cc1401bfe4c5a160 else 0x994017fb4ac3160a00bfda5640a65005fed2b1458280377eb1b4cc1401bbf595a660a00dff276d0305006ff96b681828037fc8db40c1401bfe5ada04ca00dff316d0265006ff91b681328037fcbdb4099401bfe56da04ca00dff35698305006ff9ab601328037fcd5a2099401bfe6ad1060a00dff356a8265004ffd7b699828027feb5b4e994013ff62da74ca009ffb16d2a65006ff90b6a1328037fcd1b40c1401bfe6a1a04ca00dff35098265006ff9a8481328037fcd42e099401bfe6a1504ca009ffb56c1265006ff96b6a1328037fca5b5099401bfe46da84ca009ffad6d2a65004ffd6b685328037fcd32e099401bfe699a04ca00dff34c90265006ff9a64c1328037fcd330099401bfe699504ca00dff34c88265006ff9a66a132803efcb9ae099401f7e61d734ca00fbf2eab8265007df97561d32802efebd90a99401f7e5d9874ca00fbf2e2b8265007df9875c532803efcbb2e29940177f5ec814ca009ffaf6d0b05004ffd5b685828027feb5b42c1401bfe69d6060a00dff34cd0305006ff9a6481828037fcd3260c1401bfe69d1060a00dff34c88305006ff9a7699828037fcd1b4cc1401bfe68da460a00dff34cd2305006ff9a5581828037fc85b42c1401bfe685a060a00dff34290305006ff9a14c1828037fcd2a40c1401bfe6951060a00dff342b0305006ff9a1441828027fed5b02c1401bfe5eda160a00dff34ed0b05006ff93b685828037fcd1b42c1401bfe56da160a00dff34ad0b05006ff96b685828037fcd3342c1401bfe52da160a00dff348d0b05004ffdab0c5828027fed58a2c1401fbe58d6060a00fdf34cb1b05005efd6b28d82803f7cb12c6c1401fbe5856060a00fdf2c2b1305007ef96458d82803f7cb2ac0c1401f7e69d7160a00fbf30eb8b05007df9765c582802efebd942c14017fe5ed6060a00bff35698305005ff9ab58182802ffcd5a20c14017fe4ad6060a00dff304d0265005ff93b58182802ffc9da20c14017fe42ca360a00bff25688305005ff98b44182802ffcbda20c14017fe56d1060a00bff57654b05005ff96b44182802ffc85942c14017fe42c3160a00bff21628b05005ff9ab5d982802ffcbdac6c14017fe5ed6460a00bff356b1b05005ff9ab50d82802ffcd5a62c1401bfe609a84ca00dff304d3265005ff9ab5c582802ffcd5aa2c14017fe6ac9360a00bff356b2305005ff9ab58582802ffcd5a82c1400ffe609a160a00bff35618b05005ff9ab14582802ffcd5922c14017fe2ad3060a00bff156b0305005ff8ab44182802ffcc5ae2c14017fe5ad4260a00bff236b1305004ffd1b69d328027fe8db4a99401bfe685604ca00dff342c0265006ff90b685328037fcd0b4099401bfe685304ca00dff34290265006ff9a1441328037fcd0ae099401bfe685504ca009ffb5690a65006ff)) else (if i<15 then (if i<14 then 0xfe26290a65007f798559532803ff898a82c1401efd5458160a00fef2a2a8265007ff15144182803fbca92a299401ffc6055160a00ffe2a288265007ff18154532803fbca8aca99401ffc5457160a00ffe2a2b8a65005ff51b21532803df6c3ac4c1401fbb58d6260a00fddac2b1305007eed7658982803f76b2ac4c1401efb60d824ca00f7db06b1305007bed3260582803df6a9302c1401efb6056260a00ff9ae6c1265007ddd875cd32802feebda6299401bf75cda54ca00ffb2e6b0265007fd97360132803fecb9b4099401ff65cd304ca00ffb2e688265007fd97354132803fecd32e699401ff65cd634ca00ffb350b9a65007fd98358d32803fecd0ae699401ff6695734ca00ff9a62c1265006fdd3169932803fec98ae099401ff64c5a04ca00ffb26290265007fd90b4c532803fec98a6099401ff64c5804ca00ffb262a8265007fd93158132803fec98a2099401ff669d314ca00ffb2f698a65007fd9315cd32803fecd426299401ff6695314ca00ffb34c98a65007fd9a44c532803fec95a6299401ff64c53060a00ffb30498a65007fd98b4c532803feca9a6099401ff660d534ca00ffb2b698a65007fd93154d32803fecb5a6299401ff64c5634ca00ffb262b1b05007fd9535cd32803feca5a62994017f74ec854ca00ffb15698a65005fdd3b20532802fee9d8a299401bfb609a54ca00dfdb04d3265007fe9825c132803ff4c134099401ffa4c9a060a00ffd30490265007fe9824c132803ff4c130099401ffa609504ca00ffd304b0265007fe98244132803ff4d3b0499401ffa5ed824ca00ffd276c1265007fe9a560932803ff4d330499401ffa691824ca00ffd342c1265007fe95b60932803ff4b5b0499401ffa52d824ca00ffd236c1265007fe8ab60932802ff6adac4c1401aff605a660a00ffd2a490265007bf98158182803dfcc0b40c1401efe42d8160a00ffd2a490305007bf9814c182803dfcc0a40c1401efe6051060a00ffd2a4b0305007fe95244182803dfcd3302c1401efe5ad8160a00f7f346c0b05007bf93b60582803ff4c12a499401efe4ad8160a00f7f34ec0b05007bf9a460582803dfcd2b02c1401efe5ed8160a00f7f296c0b05007bf95b60582802dfec5862c14017fb4ac854ca00f7f156c0b05006fed6268582803dfcc3ac0c1401ffa589a060a00ffd2c490305007fe9624c182803dfcc3a20c1401ffa5891060a00ffd34eb1305007fe9a358982803ff4992c4c1401ffa6956260a00ffd348b1305007fe9a158982803ff4a92c4c1401ffa6a1424ca00ffd34aa1265007fe9a650932803ff4d0a8499401ffa4c94260a00ffd2a4a1265007fe95250982803ff4b128499401ffa5894260a00ffd24290265007fe92148182803ff4c124299401efe6158160a00ffd242b1265007fe92158982803ff490a84 else 0xa1328037febb55499401bff5daaa60a00ffbb0cb9a65007fdd864c5328037fec334e99401bff619a14ca00ffdaeab1305007fed7560932803feeb0ae699401ff75d5314ca00ffdac2c1265007bfd75605828037feb0b4e99401bff5d5a660a00dffaead3265006ffd616a1328037feb0b4a99401bff5d5a160a00dffaead0a65006ffd75aa9328037fec355499401bff586aa4ca00dffac355305007fed8760932803feec3a6299401bff61da14ca00dffb0ed3265006ffd626a1328037feb134a99401bff61da160a00f7fae6c0b05007fed6360932803ff6b9ac4c1401eff58d8160a00ffdae6c1265006ffd73699828037feb9b4c99401bff58da160a00dffae6d0b05006ffd636a1328037feb9b4a99401bff5cda14ca00dffac6d3a65006ffd63685328037feb1b4a99401bff58aaa60a00ffbaca98a65007fdd655cd32803ff6b2b0499401eff5958160a00ffdae2c1265007fed71589828037feb2b42c1401bff5c5a54ca00dffae2d4265006ffd71699828037feb8b4c99401bff595a14ca00dffacad3a65006ffd65aa9328037feb155499401bff58eaa4ca00dffb0f55265006ffd71aa9328037feb8d54c1401bff58eaa60a00bffad651b05005ffd7b28582802ffeb594a994017ff5ec814ca00bffaf618b05005ffcab58d82803f7e35b42c1401f7f1eda54ca00fdf8d6c0a65005ffcab5c5828037fe1db42c1401bff0eda660a00ffd946b1305007bfca3605828037fed0946c1401bff698a360a00dffd5451b05006ffc1b6a1328037fe0db4a99401ffb285824ca00dffb5050a65006ffda5285328037fe2db42c1401ffb16d824ca00ffd836c1265007bfca5605828037fed1942c1401bff694a160a00dffd5450b05007bfc3b60582803dfe2db02c1401ffb0ed6260a00ffb90a98a65006ffc85685328037fe42d5499401ffb295824ca00dffb5052a65007bfc53605828037fe29b42c1401ffb145824ca00dff8a2d4265006ffc51aa9828037fe18d54c1401bff16eaa4ca00dff91755265006ffc1baa9828037fe1dd54c1401f3f9de6660a00f9fcef33265007fb9a450d82803fdca1a84c1401fee6914160a00ff7284a0b05007fb98450582803fdcb2282c14017ef52ca360a00bf7a9650b05007fb94b2a582803fdcd1c88c1401fee69a4460a00ff734322305007fb92191182803fdca8c88c1401fee6a2444ca00ff730522265007fb98591132803fdcd0c8899401fee486444ca00ff72a322265007fb9a691132803fdcd2c8899401fee6064460a00ff730322265007fb95291132803fdc98c88c1401ff5605314ca00f7eac2c0b05007ff18158532803dfa98b02c1401bfd4c5a160a00ffe34298b05007f795354932803ff898b02c1401ffc4c5814ca00bfea3651b05007fd5214c532803fbca9b0a99401ffc4c52160a00f) else (if i<16 then 0x17ff6ad714ca00bffb56a8a65005ffdab5d532802ffe9daa4994017ff6ac854ca00bffa76b2a65005ffd3b5c582802ffe9dae2994017ff4ed5160a00bffa76a8a65007fed5360932803ff6a9ac4c14017ff46d634ca00bffa36b1b05005ffd5b5cd32803ff698b0499401eff54d8160a00ffda62b1305006ffd3169d328037fea9b4cc1401bff54da64ca00dffa62d4265006ffd31695328037fe98b4c99401bff54da160a00dffa62d3305006ffd53685328037fea9b4e994017ff4eca160a00bffa7642a65005ffd3b14582802ffe8d946c14017ff2ad3160a00bffb16b2a65005ffd8b54532802ffe95aa2c14017ff4ad514ca00ffbb0ab9a65007fdd854c532803ff6c2b0499401bff615a74ca00dffa42d3305006ffd21699328037fe90b5099401bff615a14ca00dffb0ad0b05006ffd2169532802ffec594a994017ff56ca84ca00bffb16b0a65007fdd815cd32803feea926299401ffb605824ca00f7faa4c0b05006ffd8169d328037fea934cc1401bff549a64ca00dffb02d4265006ffd81695328037fea9342c1401bff549a14ca00bffb1650a65005ffd2b21532802ffec5862c14017ff62c514ca00bffa36b2a65005ffd5b5c582802ffeadae299401ffb545824ca00dffaa2d4265005ffd5b28582802ffe55aa2c14017ff56c814ca00bffab650a65005ffd5b0c582802ffe8d90a99401ffb845824ca00f7fcaac0b05007fee55609328037ff2ab4299401bff845a54ca00f7fc66c0b05007fee33589828037ff19b42c1401bff8cda660a00ffbd1098a65007fde885cd328037ff4434299401bffa21a74ca00effaa254b05005ffcab84582803bfe4daa2c1401dff26d514ca00bff95719b05005ffebb61532803ff75530499401bff696aa4ca00dffaa555265006ffda8aa9328037fec155499401bff69aaa4ca00dffb0b55265006ffd53aa9328037fea8d5499401bff60eaa4ca00dffb0355265006ffe88aa9328037ff2ad54994017ff46eaa60a00bffd76c0b05005ffebb54932802fff5db02994017ff5aeaa60a00bffa7755305005ffebb54582802fff5daa299401ffbaa96260a00f7fd54c0b05007feebb609328037ff19d54c1401bff686aa60a00dffb4d55305006ffda3aa9828037fe90d54c1401bff606aa60a00dffa6555305006ffd51aa9828037fe8dd54c1401bff4c6aa60a00bffd76a9a65005ffebb4c5828037ff08d54c1401bff5aeaa60a00dffa7755305006ffebb6a132802fff5db46c14017ffaeda84ca00bffd76d2a65005ffebb68582802fff5daca994017ffaed7160a00bffd76b8a65005ffebb58982802fff5dac4994017ffaed874ca00bffd76b1a65005ffebb58d82802fff5db4c994017ffaeda660a00bffad6c3a65005ffd6b5c582802ffeb5ae2994017ff5ed654ca00ffdaecc1265006ffd766 else (if i<17 then 0xc9054b429c0149f0a290504427a0133b099504ba42598127f08f504554222810c70837040541ee80edf073d038e41bd80d4b0697033b419580c6b05eb02dc416300a7704eb0235410b007630367018e40b60059302bb014740a0004bf023f01094079803a301b100ce4060802cf014d009340460021f00fb007340348017b00a9004d402480107007500334014800870035000d40001ffd605614ca00ffeb4298b05007f7d5354932803ffa98b02c1401ffd4c5814ca00fefaa6c2a65007ff53148582803fbec2aca99401fdf549514ca00ffeb02a8b05007ff58154532803fbea8aca99401ffd5457160a00ffeaa2b8a65007fdda65cd32803feeb9ac699401ff76a1734ca00ffbb06b1a65007fdda15cd32803feed2ae699401ff769d314ca00ffba62b9a65007fdda84c532803feed2a6299401ff7699314ca00ffbb0498a65007fdd8354d32803fee98aa699401ff74c5634ca00ffba62b1b05007fdd535cd32803ff6d3b0499401ffb5ed824ca00ffda76c1265007feda560932803ff6d330499401ffb685824ca00ffdab6c1265007fed6b60932803ff68db0499401ffb2ad824ca00f7fb4cc0b05007bfda360582803ff6c12a499401eff69d8160a00f7fb4ac0b05007bfcab60582803ff6d3ac4c1401ffb68d6260a00ffda64b1305007feda558982803ff6d0ac4c1401ffb5496260a00ffdb0490a65007bfd8560582803ff690ac499401ffb4856260a00dffad6d4265006ffd1b6a1328037fed335099401f7f61d734ca00fbfaeac3a65007dfd7661d32803efec3ae299401f7f5d9714ca00dffb4ed3305006ffda3699828037fed3b42c1401bff68da160a00dffb4ad0b05006ffda668582803f7ed32c6c1401fbf5896360a00fdfac2b1305007dfda75c582803efec3ae2c1401f7f5d97160a00bffb56bb305005ffd7b58d82802ffed5ac6c14017ff6ad3160a00dffb04d4265006ffd8269932802ffed5ae2c14017ff6ad5160a00bffb56b0b05005ffd2b60582802ffed5862c14017ff6ac5160a00bffb16b8b05005ffd1b589828037fed334299401bff6a1a14ca00dffb04d0a65006ffda669d328037fed434e99401bff685a74ca00dffb4cd2a65006ffda8695328037fec134a99401bff685a54ca00dffb4ed2a65007fed8360932803dfec0b0c99401eff4c98160a00f7fb0ac3a65007efd8658d32803f7eb12c699401fbf585624ca00fdfb0cb2a65007efd6259532803f7ebb2ca994017ff6ad864ca00dffb06d3a65006ffd3269982802ffed5ac2994017ff6ad764ca00bffb56b2a65005ffd7b58d32802ffe8dac4994017ff4ad654ca00bffb56c0a65005ffdab61d32802ffed5b0a99401bff60da84ca00dffb06d2a65006ffd83699328037fec1b4299401bff4c9a160a00dffb06d0b05005ffd8b5c532802ffeadb0e9940 else 0x707f1b3f791fb84fd707e8f3f391f924fc707e273f0b1f7e4fbb87dd73ee91f734fb787dab3ec71f594fa907d1f3e7b1f334f9607c873e351f104f8307bbf3dd71ee74f7187b7b3da91ecd4f6307b133d751eb04f5487a7b3d231e874f3d079bf3cc51e584f270791b3c7f1e324f170789b3c451e214f10078633c231e0d4f03078073bfb1dfc4efd877cf3bd91de24eec0772b3b811db64ed60769f3b411d994ec90761f3afb1d794eba875c33acd1d5f4eaa8752b3a811d394e9a874b73a4d1d1c4e890741f3a011cf34e748739339bb1cd64e690732b398d1cbf4e5a872ab394d1ca24e4d8725b39251c8b4e42071e738df1c6b4e338718b38b71c574e280710b387d1c3a4e1b070bb384f1c204e0b0702f38091bfd4dfc86fd337e11bec4df406f8f37b91bd84de706f27378b1bc14dde86ee337631baa4dd186e6f37291b8d4dc186de336dd1b674dae86d4b36971b474da186cfb36751b334d9786c9f36471b1f4d8a86c4336191b084d8206bf335e51aee4d7506b9735bd1ada4d6b06b47359b1aba4d5206a73350d1a704d2d0690f345b1a114cff067ab33a919c44cda0669b332119834cb386543327519334c930646f3223190d4c7d0639b31ad18c34c5e06297312518794c318616f309d18414c1706083302718004bf505f732fb117d14be505f0b2f7117ab4bcc05e132efb17704bb485d6f2ea317474b9e85cd72e4517184b8585c0f2ddb16e04b6985b232d7716b44b5685a8b2d37168e4b3c059ab2cc116534b26058fb2c6316244b0d0583f2bed15e34ae6856db2b3b158a4aba055532a83152e4a8f0543729e314de4a67052f7294f148e4a3f05187289114324a0c8501727e513df49e484ecb2745138649b984d67268d1333498e84c0f25d512d7496204ab72541128a493104953247d1231490f04843241311f648f78477b239d11c148de846d7235711a748c8845eb22cf114e489d8449f2223110448770435f218910ab484c0420720dd105548180405b1fe30fe447eb83f4b1f6d0fa347c503dcf1ed30f53479e83c8f1e1b0efd477983baf1dc30ed1476683aff1d4d0e8d473b8398f1c950e3447108382b1be90de146e5836c71b3d0d8846bd835871a970d32468c833ff19cd0cd94661832a7190f0c65462f0315b189f0c484622030e718590c22460f0304f17fb0bea45ea02f0317550b9445bf02dab16a90b3e459582c5f16090aee456c02b13155d0a984541029a3149f0a3945118282713ff09e644e9826f3134d098d44bb8256b1283092b448d823bf11b308c344568227f1119088544390216f108b0826440681fab0fa907bb43d881e8f0f15077a43b681d8b0eb10745439901c7b0e1706fe437581b470d7706b1435381a370cef06584321018af0c3d06114303817f30bd305df42ec017130b63059842c2815df0a))))) else (if i<27 then (if i<22 then (if i<20 then (if i<19 then 0x9312a58900c45762113101587b8c3b361c530db58688c31b617930af58528c277612d308f58428c1eb60ed307258370c19b60bf305b58288c11b6079303558170c09b6039301558070c01b5ff92ff257f58bf8f5fbf2fdb57ea0bf275f7f2fb557d70bdcf5ed32f6257a60bcb35e452f1857828bc035de12ee6576f8bae75d5f2ea557400b9cb5ccb2e5b572a0b9275c852e3b571a0b8bf5c512e21570d0b84b5c112de656df0b6cf5b532d8d56c18b5e35ad72d6156ab8b5335a852d3b569a0b4b35a4b2d1e568b8b42759ff2cf556770b38f59ad2ccc56610b2f759732ca6564e0b247591b2c8956410b1eb58e72c6c56328b17758ad2c4f56228b0eb58612c26560c8b03b58032bf755f68af9757bd2bd755e80af2357832bba55d98aeaf57492b9d55cb0ae3b570f2b8055bb0adaf56c32b5755a80ad2356772b3155950ac8b56372b1155820abdb55d92ae2556f0ab5b559f2abc55590aab7554d2aa2554f0aa67552b2a8b55420a9e754e52a6b55320a96754a52a45551d8a8b754472a1955078a81353ef29ed54f00a74b539129be54dd0a6d7536329aa54d18a67b5335299654c90a61f5307297f54bd8a5db52e5296e54ad8a543527b293354948a47b5229290a54800a3ef51ef28f054748a39351c128d954690a31f518128b954590a2ab5147289c544c0a24f51132885543f0a1cf50cd285c542c0a14350932842541f0a0cf5053281954078a01f500127f653f909fab4fc127d953e909f1f4f7527b653d909e9f4f47279f53cd89e4f4f19278b53c209dff4ef1277153a909d134e752733539609c874e352710538309bfb4de326ed537189b634d9d26ca536309afb4d6f26b0535489a874d35268d534489a134cfb26765337899874cb526505324898fb4c6f262d53148986f4c29260d52fe897cb4bd125db52ea097274b7f25b552d5896834b39259252c2895eb4ae1256952b2895834ab3255252a58951b4a85253b529d094cb4a572527528e894574a23250a5283093fb49e324e452688931b497924a9524f89253491b2486523f891f748ed246f52340918348b32455522889133488b243e521b890bf4851241e520b8903f4811240151fb88fb347c523d851e588f03477923af51d288e774727238951c108deb46e7236c51b288d7746ad234f51a408cf7466d232f519408c77462d230f518408bf745ed22ec517288b7745ad22cc515f88ad3455b22a3514e08a5f45212289513f889d344db2263512e08947448f221f510d887e343e921d850df886df435b218850b30853f42912132508e084534221210c50828840341db20e6506f8835f41a120cc5062882f7417320b55058882bf415120a150500826f4123208d5040081bf40c520525021080c740492017500807fff3ff71ff74ff987fbb3fcf1fe64ff287f8f3fc51fd84fe else 0x9086f8423420460fd107cb83d741e460ee9074b839141be60da106a7833f419560c4105f782ed416f60b29057782a74146609e104c782554120608b1042f820940fd607c903c781d540e6606f9035f81a140c9605f902eb816d40af60559028f813340956048902338105407560341018380ad404c6022900eb80614023600c90053801540035ffb0ffaf7fc93fdd5fee0ff6b7fad3fcc5fe58ff1b7f853fbe5fda0febf7f513f9e5fcd0fe577edb3f665fae0fd537e9b3f405f9b0fca37e3d3f175f868fc237e033efa5f798fbbb7dcf3ee05f6b0fb477d9b3ec65f5f8fadf7d613ea95f4e0fa5f7d273e8f5f458fa037ced3e6c5f310f95f7ca13e465f1f8f8d37c613e295f128f86b7c213e095efe0f7c77bdb3de65ef10f76b7bad3dcc5ee10f6f77b733db55ed88f6a77b3f3d925ec70f61b7b053d815ebd0f5bf7ad73d675eb18f56f7a9d3d445ea18f4e37a693d335e990f4ab7a473d195e890f42b7a073cff5e7c0f3b779cd3cdf5e6c0f34379933cbf5e5c0f2cf79593ca25e4d8f25b791f3c885e408f1db78d93c655e2f0f15b789f3c485e208f0e778653c2b5e0f0f067782b3c115e068f02378093c005dfe0efd377db3be35dee0ef6b77a73bc95de28ef0377793bbb5ddb8eecb775d3baa5dd18ee63771d3b8a5dc30edfb76e33b675db18ed7b76b53b565da78ed1f76873b3f5d9d8ecdb76653b2e5d950ec8b76433b1a5d880ec3b760f3b005d7e0ebd375db3ae65d6e0eb47759b3acc5d658eb0f757f3ab85d5a0eab3754b3a9e5d4b8ea3f75113a815d3b8e9cb74dd3a675d300e963749d3a415d1d0e8d774633a2d5d148e84b740b3a015cfe8e7d773e339ea5cf30e77b73a939d05ce48e6fb737539b65cd60e67b732339845cb28e5477283392e5c950e44f721f39085c808e3f371eb38f15c768e39771b738d75c680e317717138b15c568e28b713d38975c498e23b70fd387a5c350e19770c3385a5c2b0e147709b38465c180e0977043381d5c020dfdb6fbb37d35be60df136f7b37b95bda8dec36f4d379c5bc90de376f0d37825bbd8ddc36ecd375c5ba78dd2b6e87373f5b9a8dcab6e4d37225b8f0dc676e0736f35b778db4b6d9736c15b5e8dacb6d5d36aa5b488d9f76cc3365a5b298d9236c7d36375b198d8a36c3736145b068d80b6bf135f15af50d78b6b5d357d5aa78d52b6a87353c5a990d4b769ff34d15a548d20368bd34455a118d06f6829340a5a018cfef67e933ed59f48cf8767af33cd59e18cee3675d33a759d00ce57671d338759be8cdcb66cb335b59a88cd1b6685333859988cc9b663f331259858cc0f65f932f259758cb8f65b932d259658cb03656d32af59558ca9b6545329b594a0ca2764b7325159250c90b6477323459138c87f6431321159068c80b63f731f158f68c78b63b731ad58d00c58b626) else (if i<21 then 0x546c6a3295177a8a754496a21150dfa81f53e769df94e5ba71f538869bf14dcfa6d9536269ad94cefa66f5333699614c1ba5bd52d4696694b23a58352b7695694a8ba537528e6942149e7a4df525c69291492ba487523c6910147dfa39f51a768ce94657a31d518168bb945b3a2cb515e68ab9453fa285513b68989448fa22d510c6881143dfa1db50c5685f142cfa159509f684a94213a101507968391419fa091503568159408fa0034ffa67f813f979fb74fce67e213ee79f5f4f8d67c193def9ee94f6d67b313d639e9d4f47679593c8f9e334f0f678413c039ded4eef677413b839db94ed5676713b279d8b4ebe675d13ad79d5d4ea4675013a639d294e8a6741939fb9cf54e736737939ab9ccd4e5f672c139439c514e0066fb137bb9bcf4ddd66e99372f9b894dba66d99362b9b0d4d7f66bc135b79acd4d6266af1355b9a754d126684133f799e74ce9666f93353999b4cc6665f932df99614ca966511325399154c8066399319798b74c516625130ff98414c1966079301f97f54bf065f492f6f97af4bd065e492efb97514b9565c592e0f96f94b7565b712d8f96b94b5265a412d03966d4b2f659412c8396334b06657e12bc795c94ad7656692b0b95714ab1655392a7f952b4a886540929e794e54a6865309295b949f4a45651f128cf94534a22650d9284f941349f364f61279393c149d964e912737939349bf64dc126c39347499c64cc126439319498264bf125db92d9496264aa9252b928d493f649d924db9265492e64951248b923d491a64899241791fd48fa647b123bb91cf48e0646c9233b919548c3645e122df916748ac6454122839133488f64459220390f3487264341218390b3484c64241210f9079483864171209b903f481864089201b8ff947f863f891fa78fcb47de63eb91ebb8f49479a63c811e178ef7477163b391d738ea5474b63a211ce78e654728639091c5b8e194708638211bf38deb46eb637091b5b8d9f46c8635d91ac38d5946a5634d91a4f8d194682633c119c38cd3465f632c119438c93463f63191189f8c3b46136304917fb8be945e762ee9173f8b8545b862d59168f8b33458c62bf915d38acf455762a69150b8a71452e6293914738a25450b6280913e789df44e5626d9134f895d44a4624d1124b89114481623b911bf88d14461622d1113f8891443e621b910b38845441b62071100f87f943f561f590f8387ad43cf61e290f03877343b261d590e838733439261c590e1b86ff437b61bb90dd786d1436161aa10d3f8697434a61a190cef86754336619910cb78653431f618f10c4f861f430b617f10be785eb42f4617510ba385c342d7616990b2f859542c3615f90aeb856d42af615590a8385394298614710a0f84ff4278613a109bf84d74264612e90957849d42476121908fb846942306114 else 0xb71fdb756daa76cd1b627daed6d6376ae1b547da956d3d769b1b47fda256d05767c1b3abd9c16cd376619b2d7d9516c9e764a1b21bd8ed6c69762c9b123d8716c2e760f1b037d8016bf375f31af63d79d6bbe75d59ae6bd7156b7a75b51ad67d69f6b4575991ac87d6296b04757b9ab9bd5ad6ac9755e1aaafd5376a8b753f1a9b7d4af6a4475189a877d41569f774f21a75bd39369bf74d79a67bd317697b74b71a56bd29b694374999a497d22b6902747a9a39fd1c168d674649a2efd157689b74459a1f7d0db686074281a12fd083683474151a07fd025680873fc19f9fcfb567cd73e019ebfcf45678f73c119dc7cecf675d73a819d0bce6b6728738d99c2bce0166f3737199b4bcd8b66bb735599a77cd276686733b19997cca5664b731f198b7cc3b6613730499807cbe965e772ed19727cb7965ac72cc9960bcae5656272a7994fbca57651b7285993dfc9c364ce725d992c3c94164907240191cbc8cb64527221190d3c855641d720819017c7f763e871ec18f1fc76f63a471c898e03c6e1636071a818cffc66b6328718d98c2bc5f562ea716d18b3fc58562b5715418a77c51b6280713698967c493623c71161886fc41761fb70f598783c3a761c670dc986bbc343619470c2185cfc2c7615370a1984bfc23f610f707f983bbc1bd60ce705f182b7c135608d703e981b3c0b96055702718103c061602070099800bbfe55fdc6fe317ecbbf515f9b6fc717df7bed55f5d6fa817d0bbe6b5f256f8917bfbbde35ee46f6b97b27bd735ea96f4f97a47bd0f5e776f369797fbca55e456f1d978c3bc535e226f0f1785bbc255e086f00977dbbbd95de26ee1976b3bb515da46ed01766fbb295d936ec797613bb015d7c6eba975c3bad95d656ead9754fba935d486e9a9747bba2f5d046e759738fb9b35cd26e65972afb92b5c8e6e43971f3b8eb5c6b6e2c17143b8935c426e1d970cfb8595c256e0f1705bb7f55bd86de116ea3b7255b796db196d0fb6435af96d7196b0fb55b5a946d40969e7b4df5a686d2c16943b48d5a426d1a968c3b4475a1f6d0d967efb3d159e16cea16727b37959ac6cd296677b327598c6cc1165dfb2db59636cab1652fb283593d6c99964bbb24359146c83963f3b1df58e56c6d9634fb19f58c56c579629fb11d587e6c3596147b095583d6c1996097b03758146c0696017affd57f46bf515f97afb157ce6be215ee7af5957a26bcc15e2baf0757706bad15d33ae8b573b6b9715c8fae33570f6b8415c03adf356f56b7595b83ada756c36b5e15ac7ad4f569a6b46959fface5565c6b2495907ac5756246b101584bac1156016afd157d7abe355e76af01576fabaf55cd6ae495707ab7b55b96ad79567bab2355846abb955a7aab9554f6aa1154d3aa6155236a85153c3a9bb54c16a529526ba927548c6a42951f7a8ed)) else (if i<24 then (if i<23 then 0x20650da1011e1d0809b0a40a4064124204b6840d213205209210e03420600611410210411310310530b4281282281a82a16185980184d8c445208a04a08a06a1085862260061141021151011041083124203281280a82284189184104d84b4494520aa1a2122022102322906101104108136148288488088209b0a41780242640a40641240ec01c004960b341f41582a21e00b0050512511e28a8a210b80047ac0141c4b5108dc01205203209207211600e0025b059a0fa0ace00909902901903908b0070011982cd07d056484c80c824840a895842426406412420544d213203209210a1aa2423c790990190490851250d11e3f0008388a08108a880882089881882884f031843780201a40a40641240e422c01c0048341f425920520320920b211a0fa12c208e007009091261302881082081882a888929b80041c45040845440441044c42442381bc0cc15aa0ea222e00b005095071252f00580283a8489017801c02422414498bc0120520320920720b600e0024b059a0fa12cd0790290490390590882c5114482481c82c84416288a869f80047845040845440441044c40c4a8421c03819bc0021222820422a20220822620623023ce01c0cd07307006f07e084d0707607504601400201500100400503700806d07206e610a82308a08108a88088208281b884308281d01ec1e41b41d802405000805400401004c1180204791081d42201cd8429c0021220422a20223c226206210e01c0c26ace00118114102101104113103105700e06130608488a08108a8808820160230842213082e4444c0426a2a2200611411312812712d125388c8a88801845044e444494a00c22820b22227a5511e06f02124f0312730b3987f03091780f8188da869f41c4c0c2c600c21022721a288513304213618030838a20a41001851c520504800c26c2682904f02f01d09d07a10305308f28908c48223c084a1a3311148136189b1888a40c4d8c2c520626c616290313030b1185854344c0461e290250930b1221188a868cc2d4484624a1a2d0da060630202503688e8682113a3e1d1c7e8cf745a7a269d0ffe86b74287a0c1d01fe7f573ea79ed1cf27e77f73a979cf9ce2fe703737779b51cd5be693733979961cc7be61772fb79741cb5fe58f72ba79569ca8be5257285793c1c99fe4b5724a791e9c8bfe445720c78ff9c7c7e3c971da78e81c6f3e35f71a578c79c5efe2d1715878a41c503e26d7129788e1c42fe1fd70f178721c35be18d70b678531c257e111707e78389c183e0ad704378181c0a3e037701478051bfffdfeb6feb77f09bf67df996fc577df1bec3df416f9377c19bdcbdecb6f5577a29bcdfde4f6f1777839bbe7dddf6ee2776a9bb07dd696ea7774d1ba33dcff6e7277359b96bdc956e43771e1b8bbdc436e1176ff1b7cfdbd96de276ec1 else 0x550890d4423282281a82898280a164869f802c0140940541140c4b50b10a24a04a02a08a10858650150450350812d42c50d3a8128228189813802c0140540d4214084b50b1180da09a07a0ba1121aa227c06d01d04d03d0890950550d4603680e81e82e84282484c86a301b42740740f421412416435180da13a05a03a08a1120f2248c0690d51211e2680e82681e84484a214869f01b40b40741342242541d449180dc01a05a03a09a07a0ba0f600e00260be00d02d01d04d03d09d07b005087008425a2118889c0d1084a09222250730b1286844d94224346884a0e265602450713030b1a8684545c0d108703d213203209210a1b4207902904905908511a10340f484c81482484380d081d40941140d4210b0c44c61ea12a02a06a1085921a770150950450350842c90d3a89284a80a82284486a161d42540541140d0b2434d222a04a08a06a0a858616750450350550842c91150d3a81282282a84488a211940d4154214090b2444ca12a04a08a06858616650950450350850d42cb013a89284a81282284580a161d42540d4214090b2c04d80da13a03a07a1061f21a7c06d02d04d03d0530b9113e84e81680e824843082891f01b42740b41340f41741cc2d1a05a03a09a0ba13a0f210c208c06d04d03d05d0891150d3e03680e82681e84284c869f01b42741340f422c05415435180ca2426c3c06d09d02d04d08b015075124681682681e842214889b407413417422425842434fa13a03a09a10c2121aa247c06d02d04d03d05d07d083114681680e82684484b082891e42640a41240e4220b341f415c0520f602802a0da1320eac200cc81141021151011041086103881082096d0809296c041ec2a41b41d405001005427b4344c02442ad841d602212228204208210c20706609d015089036a10069388488a08108a8808825081e055c128420d892132052032102334206a101361081082082a88d08092981ec0501b42401d584018ce22820420820a211222c20701400201500100404c0ac066a100b1568388a08108a880882082d082005000805400401017c0141ec2c58402c1622820422a20220820ac207d0d81501606606ca100a00ac40319080330c18c841434198902900502b00300900a0114208814815020a100662831a86d080331205284018c624a02d4203902901904905125a103481480c824840215081a406412416422841434d20520920b210a23420600613630b1482284a81282281a16185982c00500542741ec1e58401a5021222820422a202208c207a10119136188ab0809b0c02405400402021e8402240d9021222820422a202211420700901400201500100807608d08a610508488a08108a8808843081c1982760540d82268401a4f02a01142106c4815009a108362380d0841b0c49405a840721320520320824b4) else (if i<25 then 0x2da101253081082082884288d080929c450408454410414406840e0d221222820422a202209420850d109101108a10119308488a08a8808840815081c41c450408454404410414424422841421220220821142026c691150d103105119125348688189688c8929643440440c420464bc0022822a202226206211c0c204900610410890d311512308488189288109694c2c40841040c4b4b80da07a0ba0fa1062261e7c06d04d03d0511b12630930b428688188288088c9780045045444c40c417818408405222820422a20220860a211420851130b1021041031051153c84803082089881882a86985a0018450408410c2cc48c00c22620620a61e6166114102104105a1030b37037816838928938969891f818467c0f42446c498c2cf21a2122022062325e00109114115101113103e061024803084882486985a891801845040841044c40cc24c2d0228204208210623420610911410210430ba103187a8688488088188408a1cc1001842445440442144a4351a0ba0e00c22620621061e622800610911310330b30f308488a8808845081879b01b40f41741f420c3cc44e0c942026c0c04114102115101104108a103f0370008a08108a880882081884884016083882b40184d84d0520822820422a2022082114207006136148130208388a08a884816034184544d81a05208e022602e00442b005091305053381a210b802c014244c1410bc00885600a0aa0e590713010930b228685c0d108520e23c616350d0c84c80c81c8408f4161879d42540940d4204650b1c04ea24a12a04a02a108586e00b0050250150450312542c4481482481c82c1618599c0d409405411415108d03d21320520320824b42075025045031302484c8148248188f4161859d42540541140c4950b1434ea24a12a04a02a088586e00b0050150350550212542c4481480c82482892d081940541140d4144950b1434ea04a08a06a0aa2224a6c06d01d04d03d0550890990d4603700681680e81e82e83e84484d802823803301b42740741340d422416435180dc01a05a03a07a0ba13a0f211600a08e00c11e509107912270058028428391444203d21320520320921008ca0b42094065025015045089123380a03284a8128228409448921019425409405410462448e80d22426c34065095015081355029123833481480c82484082d081f802c0101940941140d404481080ca04a08a06a10240a2271091011081481362a210954868dc0d1084a1026121a3e00130b005085072a8684479420416434805d20320920b21006ea1b420801e90990190490804250da104280a82281a840952164869d42540540d4210b2434ce02a12a08a06a1024e85921a850950150450851290d42c3a84a80a82281a164869940540d41542048d0b2434ea08a06a0aa1085921aa22750150450 else (if i<26 then 0xe009021261f004818900f80240c4201089c002102283e009021081f000840898d4202a10084250810712841810a8181084207c0023c21035040a82054103c0120225a3e0090717001030828f8024044107c0020822a3504107128205c144805c0120a2e009031201f001030820f80240c4107c002082e0090510411327000898820d4102a0820a250510712820541041c4a081e00104170008f0820e841c3c2c06e0817040f00082888143c0c1b0112d1302c8389816404414760222a20a35050a8485414220ea0a25080b0288289c1448141d424940c1a060f0305078414424d6042606907158108a0848d81a4084246c0c21225091071282854242a0815080a82054242a1208425080b0308f0848c478340c1a06090204c14360225a260490510935810981241c4c0d20a2604907158108a0840ec04410454760222a208360610813034810840d8124044106c0820825090a82054102a1015041071282054204144a1015040b0208f0820d4202a1015040a82058184204c0c23c21035080a8205410340ca0e211e088f078003c001d02d04d05d086109113684e81682684308580a891d840544580da09a07a0ba11222a1a7c06d09d04d03d08b0150d384984d909846031d030331c264050057c082c2840198e02a0c21320d206d4200cc707b00200400806d075063a100664f03781780e84e839891bc0bc0448342741e818de05a13a0e23a0d02406167d02d0430930b0422e8168268418882117420c44c3c10880f740c0da4580c60ea0cc7f02f01120a062603684e81681e82e83e84282580a701b42740741340d422434f80da05a07a0ba10a09222790215110a4484483b081242184241c6291212a2439110a89481480c824843081a40a412416422445840d20520920b202c20551290990290190461034030a88ac0544a42640a412421840ea25213203211204c206d02d01d04d09d07d08610312470370008408f0210828981c4c0c2c5c0dc002102124e06e001201052703781780e84e8398918420108415434821023ce060844e06e001081350681093603681e82e838981889879c4a0489c0ac048260130b12d1185098094244c0420e212a24310712812ab01270370008388488f0981b81b80041c4244c04d4d602260204212613670220210a88847a840c084d4823c60426a30421351511b8108389a8dc084d45c0dc0026020a08420e6148b03042180f092884508104204c0580da07a1020e25461e622712a12630930b26818839859879049a840c2c7c0dc0025a21241091301084898084944228406210260212a12630b3122603681e8409a8901879889c4784b6840c14820b4206223130a1012630b238089808424460c48c2c8230240612616410911830f30b20828888928c41044449460cc22820422a20220821142081021041081 else 0x2283e0090311411b20920980b80045046c7c002282363e0011b1141c80a83b810f80045046c6e041e001131241f0048188a892138004544907c0022824839027011283844782a0423c21287011284b8088478220e150910710141dc08424ee02211e0f0008a8920d4244c0426a1505703109285425c0c5c0022a202a0a4e00115101507240ad0800d80a03684619c0846c4506e04228236381401501ea10089099338088a88f0f8004884506a0429025057011284b80880a0ee042507701109b22109415c0c4a12e06250708a4045203c012022e00120170008e8a408108520e0842902302042182108e8b8004805c0120e2e00901170008988e8f80044c47c7c0022623e3e0011311d1f0048108988e9380044c4746e061e0090111311f270008988e8e405c0c5c0022623e3e0011311f1c8138189109114487c8582505701122121f09425c04488488a243e42c1283b808940d0b0478688a2402509703108fa210940d0b0478688a858244243e109689a0b80044c474623a88425031364421a1f216091090f842428842e0011411b1f0028388a08d9380045449c6e0225a21077021261889b8189c04223624c2117126170008e8898d408478498624e25a211b107126188d89309c044544787c0060a2123c09e02e04c07e0810711410505e05f109e1012769858702781381701c49049fc0bc0f819c0417d661e1c05c07e0811bf01f03e067020804831f01702701f02818185836238004c05c0061020e3c09e01e04e05c0710811505e109107e1011b6704f00f02602e0388a82f082883f0808daf80782045417c47b840504fc006102e02e0811405f11ee101343e80e8410ac86b0812083a1c47ac0856021b010d808938ac043a10094096486c204686b0211b158108d8ac044785c0040c2e000f000938b80048854201b03088a840a0e60a2b03a06100198320aa0e08430420b03083d808969380241d81842541cbc0040ca0ea124e00a069079097012f0050348388ac8496c1641e424480818ac0ca0ea12610460650750930123030838b80281a41e424414a22a1e000f00068403c00236200000e009071051f00482b810f8024145c01606a0a35050f004828838f802c0d41c7c0120e2e009077021a838541c34201e0012412838210800018404c202a0e6062e009081051d808968b802424c247c0121220e3e009071091f002838b80241c4507c0120e2e009077021f004838898f80241c48181941d424494ea1211070a838441c3c0120e21035093011483b03081c012102123e009081091c8089689411818c0c7c01206c0c2404e009076061f00481882021138018184107c00c0c20822645046063081a823030838d4101084e080842e0060611e104270007802420422a100380241c5c0120a2e000f005818b8003c0010024044b44a106062)))) else (if i<32 then (if i<29 then (if i<28 then 0x25e105f04f00f02701f0400a08488088208188470309b344ac486c0c62502236023e02e04e05c0711405e911125e104f0008a08f0f80044c4f4624c28820e25a4e0011411e1f0008a08f0f80044c4ec626aa1c884312550c1092a860b80241c424c2602e0090317004828b80241444c4289c002282143e0011410a18850980b80044c4287c012062282144e0011410a1f0008a0850d4282a14109901408ca1070a0a0338088a0850dc044504286a14150a0f004808b8024145c0120e2e0090214838210a41c1085c0120a2e0090717000898860f80044c4387c0022621c3e0011310c1f004810898861380044c4307c0120222621c4e0011310c1f000898870c4384d44858a18242c50e1092a85094391084a14260242c50c1090286090b14304858a18250e4421096a85090b14304858a1c250e44217000898860f8004504287c002282143e0011310c1f004808b80241c5c012022262244e001131121f004818b8024085c0120e2e001141111f0048108a8889380240c4544449c0022a2223e001131111a88854490b0424aa222814087015a1071109d338088a8888d4442a2485825110a858542c2a1e1e0090112d1f004828b80240c4807c012042e0090717004828b80241d43c7c012062e0090311510b270008a8858f80240c45043c9c002282163e0011410f1f0008a0878f80045442c7c0120422a2164e0011310b1f0048088a0879380241444c42c9c0022821e3e0011310f1a858543c2a1e151242c1096a85894442a16150b0a878780045043c6a16150b0a878542c2a1e150f0c0a00ab85d0804484c99c0445442c702942002ae16104112670111510b1b8108a0878f8004544447c0022a2163e0011510b1f000898890c51c227a113344210a228388510226c144213b109da160940c4d91087c01206270112817000910b8004984e022502122135138085c043c0022624437010c82b808b8004504887c012062282444e001141221b8086409c045206e022901702138085c084504786e0320aa0a3807066a100b108c2b80a84c848f8004984e0224e2e0090112d189805c0845c5c0022822e350770210938980b80049c4547c0120222822e47010b810640d41dc086e0417010b808640dc045204e0220283b81094082a0ae022507702140a38138238181384081050300a85029c0410849c454920ea0ee02312170317000958a4084d8108720e084270312b0421f000898908d415c0c5c0120422624247030f000898908e409415c0c7c0022624237030b8186405c0c5202e06242c11e1282b8189415c044242e062e001131035092098051082a0ae0625077011283b818b8004544054249c0120e2e00902302188db810b800c244b47c01206250711b70218980780240c5204809c0120a29011301700482a8388988d9780044c46c7c00236 else 0x40a8184785a05a03a0a05c07842840442a40240a13e1000960d810211ec211d09d0207cd0105e20921420221520104a04b06c01e09f6108701700f0270408a08108a88082f08202f884017182f083cc142c0c0d0260611e1033182a030cc143c13c05c09c0780b80fc10212204208206210603c0c22afe09e01e04e03c05c07e08109101104103108702e061147b04f01700f02701f0408108088208188470308f3782780b80781380d82042440840441040f818479ba120f1a03a1041240241061ec2003c434b01e20920220421630b0920b2468168268290110210284930818581710b2c424460420a2302e0012311e1a83a8289c020184c05600210511e15800441c4785c00a0a2103e00b032061f002828030dc084104786e0420823c310911e108488f0b800454404621023c210811e170008f00d0f8004780dc7c00e06a0e00c4e001150291f0000e08a0f80047805876001e0011e123188208f0b8004781a0621223c2e0070111e130208408f0941d4144e0100c2e005071091a83a828b800410500c26c230401a11e1b0300b098180590786c0c02c23c3606016100d04058202c180611e140308f0b80042041c7813c05c03c09c07c0b80e20420220820620a00c6100befe0006811e1f000340941d4244e0100c25075091017045921048104244c0420e26021051351380078004c0478660a084230504206618210780044c40c620225a2c09e02e04e03e05c07e08102104103105108701e061157f000828838849302780b80781181701f82041c45040845440417841042417c420134c178429a04101a09a1005e42840440809441006e09603c622c20f10712db011f00084c838f80041e4247c00a12a0e20a4e0020617003808840f80044c40c7c0022a2023e0010513000838848f8004214247c00a1200c3e007011085072082a83a848f8001a05c0002c2e00703170001488a8f801c0c10876001b000d800780141c5c0021026060f00082c840f80041e410620f21120a306970017000848941d4245c00a1221037008061283a8489c020184c0c06e23c360603741e1a8488389c02018406e17030a84b808b80141d4247c0023c2543e0011e12a1f000950a82780b80781301701f8200f04784504084544041784104a817c4238427c0023023c3e001181704f01700f020030360591fc0bc041188508540dc13418584016d5c0008c06e3606046037182782b026830b0802d99818208c26c0840b61345e0011e1351f0009a8b80b80780f01701f82045417c4d42580182019c002302603e001181301e04f01700f02702e0388c08a02f09870802fb047910816c268823c08d420084404611e0421a213030b80047444c62122502105128109109309c00220e24e2a021261093896884244ac425024f6023e02e04c05c0711405e12812712d1) else (if i<30 then 0x21842101b844c1c04423c190750512a1a848954838c48822461703088f05079c0c520e246a08341e606703507220e044b50a44834102842828942141541c6e0417010b8104479c044a10e0320e260450470250518142141641c623c100141141c405d80c290711e5091a0f6030807b01840cd80c2c06088f2820a414479420683d80c250911e1483a8208479410503d80c29075095051a83a848b0182a0aa1025095075051a84a840b0183600a0a2b0050415802838980ac01408606d600a0e3b0050515802838ac01408560080c2b0040615802030ac010184a1026c241e703120f303381a83904d8283414290a0b044d8261e1701089b06c01018560080c2b005024061a83a82080e0688420636065091a0b0507028341018585c082e0617020d802030ac010d90187600a0480c3504083205079c0c483cc0ce06a0e441e6065051a0b05070283413110a8398889414c4442601134098585c082e0617020e03054124344050730b1284282c868c0a08a0e2836c06109b05424c2c4a0a616213670112823814888d411c09414626c1000521410580c150814816030542542040c780c241ec06128489b0a0db018483d80c241ec061284a83a828f018380c15091481283a8289c020185c0024822a3e0011b114105208d893098182c0c16060b8084189813c084b5840494174e15213cc2015646060b030447a8184608120670113030581ac0454200cc1623a06082f84d882c58402c06c0c16060d080330588e8401982c423080cd4201181624701a100660b1240a40a810381380b82017036508040aa02684143418c1981a8ce0300e0cd420162581408102e08ca10089338006051c09c15c2e8400b81d4ee00160690913034838ac04340ce062a060b8086819c04540c0852123a060d030210a4254268186e0320ea0f40c4a060681303068194244206c0c170512013030581820c74200f60cc0da57010831d0803683303a9681836021a0611e1184058182c0c130411e102e304780f81b030358401c8558402286c0c16060830c0ab84b80b87d0840f03aa1c060da8402c0902a080e02e1013207942106c8a108360891b034828981a41c423ce0827010b80868182a0b20ea0e3a069055051d0338088f0c478340c23c2a060d033810941d41641c720ea0ea0a3905505a061b81482a82d0310478340c23c26060d0308408f0e8184784246c0c1606088f048143a03a0807842a0d2c20128720421506561008a29840780b8138144501780bb840c2c17d2c0d21023089086061b0306414c1241066101e060f04f0170208a02f185f0808f2342012812c8d1840904dc05c09c102280bc0be623c2023c941ee06130308f09818c224206c0c611210341ee061184868194204786428460c201604606908130308f08c224218186c0c609208320411e150303 else (if i<31 then 0x113027003808840f80240dc084109c00e0222826047021049111f0038108a882138014045c00e022103e00902701130270038088989813801c044247c01202e042084e009057011131082c80b80a838f801c084106e042092243902702505198488f0941c414c106a1220e60a3e0011e12838849820c414c10540c23c602330110730819810829820cc204785413c05c03c0941021022822a0bc213c2023cce001131071f0008a88f0c41c4985c0022823c3e0011317004811810f8001a05c0120a2e0006814808980b80240c4807c000d02e009030681f000340b8004541a07c00a04a0230681251700482834089938024044107c00a042e00104170008a09b0f80044c5207c01204210330811e17001820340f8003c0023c230411e17000340b8014204787600a022b00505158028208068223ce0427010b8184023c608e04a0a441e703120f303381a83900582e0210284a83884c1c044011e0b8105c0c2e04111e304507180c2047941c621017010884984380a83900582e0610282a84a838c0e0688425055075091b810541141c40606507138105c0422461308509120d04478c21414683417010a823812828d411c094246248111b907120e0446c2838184211f108ec16084950a4508423a21254291034041a0283cc0ca0a30680b032848b802414c2541492066070843e00907507308270048109b0e41dc005c0120e2b0050217004828b802404c04720660708430699077001b015802810f80240c4107c00a1221030697008061f00481a8288412405c020187c002102e0010410820a44160f8004105c00602208390530310882c27004808820ec010d9018680c24a2e0013610818840a44160f802408420760080c240612516030607b0184a0aa1025040a83a820ac004145600a0e2b00501100f3818230d05828341701128108f04478460423ce0426a311e0a0e04478203c08d20a3e009075073082700480a849809281841456000d280c3b005024061d802030ac00199018760006c80c3e009013081052580280a030c4782a1023120a311e7011482b8109aa8213800c04414760080c2b03042100024e150950790518047820cc142908333032848dc042a10a1225087015071b8085c0c3c13c05c02c09c07c10212204202206211c0c23cdb0050514818a44210ec0041c5600a0e2e0090750730823015802810f802408c0941c803d60020e350811e100f3818210d068223c254211e7021380893884782a12a10202e037101701bb030c47822541702123138088889c0c4844e022602703442100f381821303110a4223c14160a0b0780240c4247600a0480c3b000664061d80031a030ec01405018760080c2b000694061f00084884245220b0780c19075041083878004d8424760086c80c340612d170048128388492c014090186a0811 else 0x60d22b033080691d818030348c0181a4400c0d22e0011401c1f0000d0b82780b80781380c42440840441040c0181a417dae02130870117003808b800c24c207c0021227020b8187801c085c05c080cc2280bc61261600c1649e09e01a04e03c05c07e08109101103108114e066f0008a0148f8004504d8760606ce043b03036a061f0008a00b0f8004500686604e022309b02118458108c0dc044613606210991211845818b8014084540a49c00a0406e3e007027031f00581b8118213802c0d4080189c00a0400c3e00502016180e09a8b8014080187c03c0680bc1020220621000d21a100a70270115811823808f801c085c006136046084e009021091f003810b802c08c20c108e04130470213813818ac08c11c0c7c100be2100cc61e623c207e0906930b00630f0b237000848828f8008185c006022e0011e17001820a408c084d47c0023c2e001111051f000838828f8008185c0021620e3e0030417001820b8004785c006042d08e0806630f311e10370008a88f0f800c0cc207c0022a60620e4e00115308105270008a88f0f8004504787c0022a23c3e0030317004818848f8004145c0023c602390211e304126270008f0b800c0c46076042e00302303180f3030b800c0c41c660721a2e003031071f000828b800c084147c0022823c3e0011e170000b080798185c0022823c3d08e0806630f61031121a380f3030b8000585c00110990d1082c888b8003c001e00309302188398508414c2c5c0022a60420a4e00301158107800c0846121e009021091988878004245c0120220a3e009011051f0008a08f180938004504787c001e00302118407800340c1a060f0004c08c105c001e0009021810b800454c2441c820e24c290d0f000780041c5c00a0e2e0010517004838b8024044b4740c11073091083985884b4321a1e0011312828780241c52022602e009031081f000780240c410621121a2e00115170008a8820f8014045c002102e0090250710821858541c3c0120221250f004808828f800410420921a290250717001828941441cc106a0a20e6103e0008839820841cc20540c110730417001840b80b80781281445045417842441441c0b80b025dbc0020e60a3e005070421f0008a88f0f80044c4247c0023c6023e003021091f001810828e408c084d47c0021020e3e0090717000918b80042041c7c012062e009031231f000840b80240c4207c00228246330b0985878014085c002102e009021091f0008a8918f80044c48c7c0024629015091700482889884138024044106a0a110891217004810840cc24478460823c25071053081a838849828c47a818420a6122507109305190208f08424c20420a6102e0011511e1f0008998088393802409c047c00e0426a3e007011301f003808980f801c084d47c01206e023e0090370))) else (if i<34 then (if i<33 then 0x5b011b815808ac0436021504702b011d8185c0ac0c56061b030c84a82d818f80240d411c08c0cbc00a086072124e009035013032700481a80980924154148180789c0100ca1040c4e009055053092700483a8218213801414c0640486161e009035053032701049702040182833185f082380820381024841c198c2f8411c07c0a11861e617c0c6e02e04e03605c07105111e061254f01302701f02e03882088f03092a7800199c0c60c6e022e007011380d080819a84040d34202702036a101b815080819a8405c000cca063e000695031f002808b80140940c7813c09c07c0b80fc1020820620a21022a229c0cde09601e04e03c05c07e08109104103108114e066b04f00f02701e02e03f0408088208188408a7033582780b80780f01701f82040440c420408018179ae060cc206630515819848330ec0c018198600c0cc2e0011401c1f0000d0b81382017841017c422434c4419b8414e0217030f003808b80a81380f01701f82042440c42040b8184b59c13c05c09c0780b80f41021220420820622bc0cde0011401c1d81b808a818360740c2e001150371f0008a80d0f8004540586612e022e0001c507105270048388f0f80043cc107c0021e6083d08e0806631130fe1037000851808c818498461024c2e00301103304070210d985e030931848592702780781380f81701e82041040c414404453819b813c05c03c07c0b80f41020620a20420200c0bcdc09e02e04e03e05c07a08102104103105115e066f0008a0148c18dc0440c740c2e00b03115042270008a00b0f80045405866056022305b011182d8188c0dc045c00a0422a0524e0070117003809840f800c214040189c01606a020844e005020061f0028100b0f8004540a47c00a0200c3809e02e04e03e0540710210410310500630b05f6b80b810ac04c21c087c00e022e00b0130830527003813808f802c05c08c20c10ae0213087011380b818ac04c21c0c7c05c082282040bc20860a0cc617c20ae0510508c30f30be10370008a9828f800c1440f1c0824bc1024e44fe0425a05c60bc20b30530117000859030f80042c41c7c0022a6063e0011550930427004839840e41cc20c08626060224c3119e04097e0511b21b12602ee1030b06a5f0008a0290f800c0c46116022e0030111844888b80240d4144249c0022a6063e00303103170202e704781780817182b08278004245c0060220e3e001141071f0003408c0e8185c0022a070302e606170000b0b8000585c00112612d17000898b8003c001e00301128284c443c006022e00302301198287800c145c001e0030130519809840b8003c001a063011503078003c00130190d108498608424c2c5c13c03c09c0780b80ec10212202208206229c0cde09e02e01e03c05c0760810910110310200605e6f0008a8148f8000dc4e0 else 0xe00113301183bf0203ef04109781780817182b08281a3813c082480b8c2c908f40c13120b8085c042a10a12200a40542541e448629011480a84489085202e0211487021284380a838c521c044a08e052243040f701702304f080529818f80b81380f815c041b0fc006022066e02e04e036050a53604f01702701882b02836042a3800c145c0020e20a3e00305170008f0825b81025c1a7c0bc041b00b8c178415c13c05c0820fc2003c14a7e0011e17001828b80041c4147c006022e003031201f01701f028403020529b8008185c006082e0011e17001820b800c105c006082e00301118109a8b800c085a03c024606120d82600cc61fc209e04e03e05e080a24220a5063702b01e065831f01702701b02f030981c18f80b81380f814c2f8184b500c7c09c07c0a615c0c2607063e02604e03e05509e061304701700f02704033282f081f80b81380f82041c29418d0aac078195c05c03c09c060d820e2122610600cdc0cbe02e01e03e0508006c107135109130830435e066831f01702701f028980529f80428b81382041505c498199c0b841503cc13c03c10605c2026a781ee09e01e04a08126e1050d4700f01f0438109a8511b8014085c0024ca043b037021700403581a81181178014085c00604a043b020f00480a8118112c083c00a0e6032024b020d81078084c380781041441c1981b01a78415c05c09c0621026014a6e001261581a8380f1841007a8181187c01210e06a0e401eb03308507a062f002838b80141c5c0061024a3e0001617004839840e421c0941c6610a0f6043e009073081f00483b811841380241cc207c0120e61035070c037001030d41c3c01210e02a0e480650430401e2700182284c821380242141c7c01208a0e6104e009085071984283d808cc044c0521a19080425071e84704036033188987f081d41cc205c04101c0861224c0cc617c208e0930b06930fe102f00f01f040330848511b80b81380f01418c4278184c11c00a0a2e00b0350530927002849828f802415414c249c016060843e0003717002828b8014145c00a0a2e009053091f00484a828d4143c0120ae046124e009053091f004829848f802414c247c01212e04a0a4e009095051c84b81a828f802425c054148612a0a2063e03e051091300a23701702701f028840928529e415410c100789c0024a2e005073081f00484380a8391411c0a8187c01606a0e3308a060461f0000b0b8014105c00a08230b0f004842838f80241cc207c01210e02a0e4e00904b025053092b80a838b80241cc207c0120e6103e009077023082700484380a8393802421c0541c9c01210e02a0e4e02e0412630506630be103e84704033188987f081941cc2c5c05c09c07c0a20226010a7e00502138087802019404c049c01606a023e0050217002808ac043602190950) else (if i<35 then 0xc12a240f103025095120788184d4128258a2301360782604c061152062150792e0308a10310a0848369b01a0d846c450818850414f80c0c621242a2505c0681e1052151282e0341b09108a10310a1b01a07841c85449cb80c24e22a40c20e102681e215128e061272f0310a8940318889701a0d845047881891cd80c10424c28848820e25a7c0683611411e206244360321b08a08f1031219a415819828700cc14228214132580660611410a0732c0330308a0850399680a409819844813b20ec2214a4806836606611114111340330888a88884e964058184b583c920ac0cc1e3a0290260660b201b483b033079241581982c6c0c158c1e380683660611410b60b340330308a03db07960198184501ed83cb00cc0c22a0ecc16580690260611507660b3403480b0308a03db079a0198184501ed83cb00cc0c2280f6c1e58066061151110882c0330308a83b305960198184541d982cb20bc0c4443036606074126230308a03a0911201981891c450488b00c0ccc0c850e0258069026064287012c03480b03058b81158190d8498620ae02c0c84e490160612d03620500190528981041781905c700c22822e12086c58066067020a920984030502190938429a01a40581845045d0d8d00c0ccc0c84ee025417e0608a7022403034b0320bb81160180d981909dc04b00c0d2c0c84ee0258069026064277012c0321408082588a958058182247204c0c604486460630912d234204485281a098124158180e86c0c26007414a4806434130079240330308a21d036960198184501b50e8b00cc0c0da874228580660611406d43a2b00c0330308a83c9601a0d981845049090ccc0300cc0c22a0f2580642810104b1152c0308082508aa13960198184881d0450b00cc0c2280da874580660611443a06d2c0330308a89383f178180b889dc044b4bc0c05c43620ee0424c601e224e06701260321b08d90d8931701819845c85c498a05c60a213c0c44e5e0609b1703045084c38182c01b0805c611c0c43620e5e0609b12760505f2831b0330288a92c0581841d8144b4a05d20e212c0a0d85a0590790960670105f09b3d02d0348388ac84b030319e81a41e425818414134c0b8c11c0c305c11b608e062482b033040839281a82241d818170b40d41120ec0c0b8e046062124604e062484984b022211242582041d108920e21205c0d84a0890760605c2422d03504483b0302e3811a81a41d81842017c16cd210c0c2120cc46066041090752480b033028839241c1081981b0900cc088840c40be580611e1040544422c82b033020e81a811818188920e0cc0d8380690160406205f2c82b033020e019819810170900cc0c2080b6480660610504d202508f2210d8181284787c0c0782e0603c1603050db018462411123053031f001840811441cc0c608a6106063 else (if i<36 then 0x41e302e061c033030330e01a4090a8424178b00cc0c13c622480606942a10905f2c034808828360581601a40441417c2c0b80d06c22823c40c6026c0683611411e206241370304a89078c0b8187c0c15a2c0620630208a27030330b01907a80445441c818c24e10220e12824c441ee0690d09423028400408361041c8190781788c0c1000ca390160609812d260340f103033985942041b04b42a8980c40d21a15a4105e060691c838420360d8181b84c0294900c06cc0c0d321a50960901150842202c0330308a882141998184201a417cb00d2042100d20bc530be060ab1c80b0302f04b0421449425c2942401b8ac0c2080d20bc403660690d086218290304b83311078c100ab818810212c0ca302ee0609706906c2f035028839828171161b0184544788d01fcac1223c40c6020bc540710920630205e288290318120f02f144d6409818c08904ac1320ec0c39056062231c0341b30308a0919209a01818d819060c2cac0c21014a156406660610841805f2b04b0309182f1240581841108c178b00d2042108300bc5309e0611e2232182111f0308f130184544788c41fcac13405204c0ce02501e1076067024352c82b80f031181381841dc081b10d4ac1300d06cc0ce022282607806063606702435911340330338108a88221a98199819c044208c017ccc1300d204e020bc260690160670210443505e3034b0338108221a82f18c278184788c0883c60805dc0c4305066e061e0303488f1031119701a8044544781fca10740414220e24c1006c0611411e2068362b02304482b03118118201d58181781a0c0d040c1001184e0602e22c183308f10311182f14c1047b81822880cc0d040c0ca100506650811ee0623006c3482b03184a829181141cc201d48c08100260406205e1c8130302e02f9241d41cc201989202c0a120a1260258069013081050b02c033029808828481641d41cc201989405204c0c604a0e58060b01090b2240341b30308489b140b82611c0c05c308004960606c202482f3030f8180b8c14780c24623c40c404b10711e188f381082025045150d5c0841012c478a23c2120940cc406610904b11e208a88082503d1182601981847848ca11420809423c460460807560611e068321508482508f11819c044784c02c0b00c2120a8360406205e188402d8170361026c41c0f04c0903c20a09626a4c0613011e0b0201708082b0969041441c4240b8134a40c0ea0bc307511e2060682580b03025883896940ba41c0f04241b0ac0c09620f212410504d081182fb8088401e04d944544040f018c820a0780cc310804b41805f238088401e21802f9601907842441412cac08c100eac0c0bc0d06e0605b130302f83704b9207841c818128258a12e40c2120be102510805b05f1b80f0302b0f818134423c2540cc078411e06603 else 0x60350098084c93818c14198780c20a03c3e0630505f0662504882a0f7031301a824415078860a0be0cc3c06a01301099260320f50408381a9781a810c102000c0b80cc134086084c06089a01608301284618105101d09a9701a0d9810c080e8ac0d604152301e602901a065023010273b030335810f01807a80640541cc04cc0c0d36043e0608ab021c83b0318401b1281805d41d8181a6c08d20ec0c6100cc401e9076067023082c839847030559381841c1981b0980c03d208a0e0546086904a065073040692e0300f503013a83d8098204c040c84c0294b80c02ec0c11521a59056060363092484a82b0304591415818198603d20ae04613c0c5905309e0609e2482b0318483492424199415819c08b212a0ac0c0c649095056067010b02a8281700f7031241cc2381818c920ec0c6100cc4904a06035b023040660803c83b031840589241d819c08c20806061605dc0c460608eb011b030335808e8180a141581807ac04cc0ce0415d6024e0609bb011d0328230301ab81031d809e416818061414c20198d20e060a08c0c046608601e0285053010a52e0330300c031985978182784e03c0c1603a0660609e7012081082c0f03a130180d890443cc10b80c06c2146024c06036126308260301b1051809281981823ac04940c0c6c0c0cd6025a06b016060b17022d0358098285802f96c05819c08c10178b40cc0c136e024e063050631980982f030319381842c41c1b018cbc0c6101623083907302308e0602236030418981051808931b818238410224c14e25a4e0609e1180f030580e0198181986623c0c13c3301e060b11981180f030f81826c580c40c6021364e06066170304608c0781a4342c4980c0c640c6160725a066060ab701250303483318402f960181a442419817cb40cc0c152e024a06036606066b022d0301b303034d811681ac09819c04940d6040cc6080bc590205e109066e062d0358103498202f168180d8229c08820bc0c054309d2113010a527030838360331301a0da4084d4904c08d80d03c42220a4c0601e028105260340f014083930181fc844c10980c83c0506084c0643620a302270304f0a0180d98190aa434b00c0c6c0c83d2225e060ab170305489078c24c0b818903c40c61414e4c0681e20603930b2e0320f08a88290318118c078182c07c0c1382))))))
def combl11 : Packing := (2605,4,8,12,4,17,0,combd11)
def combd12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3ffda84ca00fff60d32803ffd824ca00fff68532803ffda74ca00fff69532803ffd314ca00fff4c582803ffd534ca00fff61532803ffd2160a00fff48532803ffd814ca00fff60582803ffd524ca00fff54582803ffd514ca00fff95532803ffe114ca00fff84582803ffe3360a00fffa2132803ffeaa4ca00fffaa982803ffd7660a00fff5d932803ffd864ca00fff58532803ffd6160a00fff5d532803ffd874ca00fff58932803ffd6260a00fff58d82803ffd734ca00fff58d32803ffd7160a00fff5c532803ffd654ca00fff28d82803ffca84ca00fff28532803ffca160a00fff21532803ffca54ca00fff20532803ffc3160a00fff14582803ffc514ca00ff75cd32803fdd314ca00ffb60932803bfd8160a00ffb58982802ffda84ca00bff69932802ffda660a00bff68582803ff9a060a00ffe4c182803ff92060a00ffe58182803ff91060a00ffe68d82803ff9a660a00ffe69182803ff9a160a00bff68532802ffda74ca00bff69532803ff9604ca00ffe60132803ff9a04ca00ffe4c132803ff9204ca00ffe44132803ff9704ca00ffe54132803ff9a64ca00ffe6a132803ff9834ca00ffe60932803ff9a14ca00ffe69d32803ff9a44ca00ffe69532803ff9314ca00ffe4c582803ff9534ca00ffe61532803ff92160a00ffe48532803ff9814ca00ffe60582803ff9524ca00ffe54582803ff9514ca00ffe95532803ffa1160a00ffd84532803ffa114ca00ffd84582803fde334ca00ffe8cd82803fde3360a00ffb88982803fee224ca00ffea2132803bfe884ca00f7f9dd32803efe6660a00fbf999328037fca960a00ffe2a582803ff8a94ca00ffeaa932802ffeaa4ca00ffeaa982802ffeaa60a00ffe5d982803ff9764ca00ffe59132803ff96460a00ffe5d132803ff94360a00ffe61932803ff9614ca00ffe58582803ff9754ca00ffe61d32803ff9624ca00ffe58982803ff96360a00ffe5cd32803ff9634ca00ffe61132803ff9424ca00ffe50982803ff97160a00ffe5c532803ff9654ca00ffe50532803ff94160a00ffe55132803ff8a360a00ffe2a132803ff8a14ca00ffe28582803ff8854ca00ffe29532803ff8814ca00ffe0c582803ff85160a00ffe14532803ff89360a00ffe26132803ff8914ca00ffe24582803ff8954ca00fee91182803fba444ca00ff65cd32803fd9314ca00ffa60932803bf98160a00ffa58982803fe9424ca00bfe68182802ff9a04ca00bfe6a132802ff9a64ca00bfe69982802ff9a460a00bfe68582802ff9a14ca00bfe69d32802ff9a44ca00bfe69532803f7a554ca00ffc84532803ff21160a00ff68cd32803fda3360a00ffa88932803fea2260a00efea2132803dfa774ca00fbe99982803efa664ca009ff2a582802ff8a960a009ff2a532802ff8a94ca00bfeaa932802ffaaa60a00 else 0x4c06142681501a08c2581301608c0c8f045084ca0540682505604c0582305a1341c16045420da1340a80d08612c0980b086064781f0426606e05c0684d0740c41c84b124905c0c521889362907c0c521859362f02e0742683a062121a083b0b4c06a0741683d0840c10987b114e0661e520701a81504a0741683842612c2d301a81504a1341d0330b624880d40e82d09a0e81987b0b4406a1340e82d07084c3d85a281501a0942683d08420c15140a82505a0f421083113d09a0541282d07420c2cf40a82505a1341d0830b3d09a0341683d08420c3cf41284312a23435081a84d04a11c0b809124205451c049330fc0c544869b0010820fc0f0350d6167c0042421105e0581988d12460021041f81e06a1ac2cf81b8170325ac2c889981f012a2108841082908a2343508180f10920842282f01a1a84118008202c21181988d12a1a82124101610860381a8950d26092080b082f0322ac2f0350d222960641082908a23434211f001012080b082d11e0781a86b0b560021241016606a2543585a08482c2104db8091461f81a8910d510920842380912a1a0b0f8008490205842187f01c0d44a86ab00509a10c0380e0660944a86a700509a08c0380e0661144a86a700504a0ac0381e0661144686a684d04a1143780e0626c449180282042a10c0381e0660b44686aa84d04a1144b80e06290435141282d08e0781a8890d3e00a0942180701c0cc268950d4d09a11c0f80b0fc0c434a8a282505e06c2f0350d2227a08c4585e06a25435809c0a01500201002808a1a18c33210510420a42288d0d420602a19b808694200d8c42481104211c049b2103e0021241016103210c0282d0de03818a8b30010405841484300e0781a88d0d55f0cbd33786eed45d40b9016f86dc7db3db5696906cc0d8b6afed5de2b88565bab4d53c6a02d32fa521481e8aed09d9fe73dd6770ce4d9b893546674cc7698072d3a54cc9e4925f234a409475d8d5117ce2bac52389b9117a20643ba868f0b5213bc23083910556076c07a8024fea9f963eae7c60f721e9a3ca07818ede1d82bab374ace761ca7b8bb704eddf5b6f36766c1cd5e9a6db4476750ccd5956320262c6c36985a308e5ff4bd9975e2e1d5abab2f960a2b545580a8594b628ac50309e1137826514b9094a524523f646da8b91122a1b1426682d50109fda3efa7d88f7d1e713bfc7658e971cd1391470b4e039b9f366e6b3cd391a1532ec635cc2c97ba2efc5b7cb2b161a2b2253c8a29939e262a4a048fc119022a84460858104820443ee87ae8f001d4639186fa0da21aa033f865b8c5a18262f045b20b1215962a6852989f6133224c4464887710081e9c39a06e20cde181c2cf853709b4119c20503b806a00bcc150824f03b806540a700fc00e60003ffda360a00fff69982803ffda160a00fff6993280) else (if i<3 then 0x7606a0b41d82311e05c0d85842602ac0047984d05a0ec1021308e05c0781e06640623c42681501a0942103302602c118412a20e449e47a80d04a0742180b04084c0d8460621241486bb00505a0e4798430960810b81701e078198c0b031511b0308454478038111e60941683b09084c2380f03605819b42681501a0847984b02602c130310820e449b80281501a0940d82b02602c1181e06a1341d840427c06a1340a8091ea1081984b02602c2082107224ec0140a80b0960940e82d07a10c0980b036118188f123085180d40682503a0a42103301608c0d82918212435d01a84d01a0940c8f108612c05823030844608290d7e00a0540682503a0b41d84b08604c1181e0623cc04211308d02a0940e82908604c1181b05c0c4c0839116c06a134048f104a0742184b01606c202113520a435f80281501a0741582308604c0581b05c0d426838687e06c0142681501a0741683b04610c2581301606478210688d09a0340e82d07a10c2580b036118188f30f6d02a0940e82d09604c1181b05a0f81884b0b6d09c1340b01501c0341302505a0ec220f6106d09a0541281d05a0ec25813046064170311e616ea0580a80e01a0981282e05a1341d846106509c1340b01501c0341302508c1041c0f105c20ea0540682509a0f42181301608c230310920ec49d40b01501c0341302509a0f423043050cd841b40700d04c0941702d08c100b88490dc20ca1382680e01a098128460820a07886e106502a0940e82d07a10c098230320ec230311e622ea0580a80e01a0981282d07a1182184c1ec20da1382680e01a098128460806c437082e81602a0981282e0580f42304111c20ba1382681602a0981282d07a118220f301c20d04c26c46063420198d42683b0460ac238170142084204d8581984b0160841c82b0826c52138270260821241084505a1bc0459136c20cc00c1182b08e05c0781e06a0f425581302e0820841484511a1b841301a82503a0b4210311121ac29301a84d04a074202110d6148a1340a82508618108d40a82505a100b108111618861c108a88e81501a0942683d084200b1892603502a0940e82d07a1010988a603509a0541281d05a0e10985a603502a0940e82a06222c2d101a84d01a074202110d61e880d40682503a104508f301608c0d84122084435d01a84d04a0742184b046064a082b0808443580ba82503a0b4218230360ac230310d222ba0541281d0824e8198130460641d8412d084445c41f033022244d8b01a84d02a0942103309604c1093b0820e44980b884d02a0341181d08604c058230823c109840c8290d084520b40682505a104ad80b0460ac208490d420c80d40682503a0a81884b01608c0d8291b24c435d01a84d01a0940c8f309602c118191b24c10886ba03509a0540e82d07a1045584b02606c208f12408 else (if i<4 then 0xe0d0c25813014088220f06c23c2cf084e84e090f140700d08c10c2580b0883c47987e107069c1380b02309604c1082892c0cc2c593281602a0981282e05604c11829071244244de10616fa0580a80e01a0981284608604c058230821241c33305c211a0580840504c094230430260841d8411e0cd84188bf04e01c08c2580b0420e41703136164bc098170403c608c158402ee05c0683d09c20d0c741302505c0b423040b415e44486e10614da1382452504c09423040af21a0d9856106502c0423682604a118220f311c20aa1382681602a098120f30bc209a0580a82604a0b81431911c20c2d542704d01c034230410d06cc3f082a80e01a0981284608228c058230823c8881b0a221b842142704d04c0942304309608c205282820a07886b01c210a0981282e05a11821823056100b852828212c0486e108502c0541302508c10c098210761018c9392d064447084304e01c0982083b02c204d9142704d02c0541302508c10c258130461009c8381e603842340700d04c0941702909602c11828832360e83610dc210a1382680e01a0981184b016084788d8360741b086e108509c1340b01508c10c25813080bc4911241e23cc0708404b60412f8238170120e4241761060ab10181082e0626cc44591f04e0420ec2f081363068c0825f02909e042488382e6178417423040420ccc3f08311381ec121e300e0661e2c8e19b01080c0810849309c0cc2c592a81602a09810490666178418286a508ca0b8143030bc20c3c352034e09617819878b23609c098209370126c2cc86e104e09c038128690820e1a4590afc20ac098208486620bc0a82b11c209c0981484030e0343483b0815f8415813028286164b7810b522384138130406620842282b11a1b8412c070209121241282b0b151434986105e04c0a18c8210522ac2e868a82238417813028a520241082b08a2343451e105d09a0ec1182b08e05c04172104d02a0341284302602c1184509a0e81421210682ea0341282d0808cc058230561042486a106d02a0941684115604c11829076100a5081116d02a0341282b02602c1182d09a0e8200b2106e0060b42683b04611c0b80f03c0ca608c1703702e06c2c889e84d07608c2381701624841180380d09a0ec2182305e05c0d80e065e09c03810529092024128686916428f083304e04c100d8849042104538090d14c4db0837048a2c1042481108609c068288da1a293083684d02a0941683d0822ac25813046100a48f301420fa0540682505a0f42181301608c201ba0923c841d41683b09608c238170103c841342681501a094218181e40c109342680d04a10c2580b0408cc200f10521a841b42681501a0941683b09604c058220823c059083a84d01a094208a309602c118411e03884086b684d02a0341683d08612c0980b084084780d21 else 0x60460b82182308e05c04336104878c0981582305603c0985863c20ae0381302b080d8c1182b01e0426f082c0f3010f181182311e04c2c3d6105309c0982182308e05c04336104d02c0540700d04c0942304302602c118401e2120a883e108d01c0341302508c10c05823082124143310dc20ec1380b00e040d3818591f04b02c038130461026c703c20304b04c10c2581308e05c04456106609c058070210820a41c34e06164aa0580a80e01a0981102909604c05821070cc25c3486cc211a1382681602a0380684608612c0980b080bc0fc8210703d84248268160212340700d08c10c0980b080bd0788f2230c1842340700d04c094170281805d8408686a581ec138070201840c1a8868b24a09a0580a80e01a09811813046030783611e4604c3084281602a0981282e05604c118282e0be42018107223842142704d01c0342304309602c202f01e2080d48290dc21081340b01501c0341702c070d04258130160a41c59a04100820360b5c215a13826816021514070085)))
def combl12 : Packing := (199,3,8,12,4,15,0,combd12)
def combd13 (i : Nat) : Nat := 0x4120441605422084450d84120f21304a09022110420b80a1b082e004110542303819114351002128221180c0c8921a88eaa8aa00ffec1401ffd32803ff305007fe4ca00
def combl13 : Packing := (4,2,8,8,4,9,0,combd13)
def combsamples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe86010c810c27c8ca50f647b46bc62c74e0490045218d51f27414cc2501cf9c030a827f39c04a3,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffece010c810c24c0c841f247344ac60c64e0090015218850b054144c25000e8c0302827d38404a3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff52be3411344a7f88242d3849b5018f0c16ffd19d0a081c4228029280586c61ffe05d828365b4d,0x303e0014b00a3f00880d3849b50182881cf6ec00ce700e422802928058206084705d828135148),(0x8c965810d0c1f044341006903f8b8000218000089007bf0d81e8685bfd43995871965578cae1e,0x1088083ca4440403076100680087600000000018b308fd10d81e8605e8141195801a0557ccae14),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3f6ae2087bb18c078781d30801b00184616ffeb4400180904005e7fd6026a485dc4823e4340fb,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec7000c35b3b78c068181d10fc38001846199143407400090400588a16026a483fc002280340eb),(0x10fefb48630422314e4c28a8303f401358662fc840012b6f8375335297d153f0017d8c4f8bb74,0x130fef34a400823312e0c28803039c0131866abcad831ab4f83ea33529fd15378017d80478bb14),(0x17cf0c6027309371c908842c160b2b39e1027ae05d7814e4c8b1068b2516e08bd6182d6bebdc,0x101f0f212025309371c0010ca8121b293031437aa0647814d8889105872510108bd6182c6bea5c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5e01f9a045dd4200058bb0d7429479780311139c2a25c13197a919ba26d6133a8ea038be8b4b7,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfc1faa345d5c0100582c096429c39340301139e218d813dd7ad097926d6133a8ca0383e8a2b7),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb70e8c06818c12c081e8cc17ea08598ddce2887490502e86fe7e8d810ea8a6a7460ef801071a3,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef60f0c25898c16c881e8e8157288490cdce28854c9302e9276168f810caca6a7420e2801011a3),(0x263f016008180d38cb8661243640464a8c40c84a2422679b33d226068938484403bf650179500,0x300e0148080832c8620428203c4044488c60c841d8307e022052660689084844021e450141500)]
def combcolumns : IndexTree ColumnInfo := (.fork 91 (.fork 45 (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(0,0,383,128,14),(64,0,447,0,13)]) (.leaf [(128,0,383,0,13),(16,0,495,0,13),(32,0,351,128,12)])) (.fork 3 (.leaf [(8,0,503,0,12),(1,0,494,16,12),(4,0,507,0,12)]) (.leaf [(2,0,445,64,12),(256,0,255,0,12),(192,0,319,0,11)]))) (.fork 5 (.fork 2 (.leaf [(66,0,445,0,11),(80,0,431,0,11)]) (.leaf [(132,0,379,0,11),(144,0,367,0,11),(160,0,351,0,11)])) (.fork 3 (.leaf [(17,0,494,0,11),(320,0,191,0,11),(24,0,487,0,11)]) (.leaf [(0,16,486,9,10),(0,128,347,36,10),(0,64,189,258,10)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(3,0,508,0,9),(136,0,371,4,9)]) (.leaf [(6,0,505,0,9),(32,128,347,4,9),(33,0,478,0,9)])) (.fork 3 (.leaf [(130,0,313,68,9),(129,0,334,48,9),(18,0,428,65,9)]) (.leaf [(12,0,499,0,9),(48,0,462,1,9),(8,16,486,1,9)]))) (.fork 6 (.fork 3 (.leaf [(272,0,167,72,9),(384,0,31,96,9),(288,0,31,192,9)]) (.leaf [(96,0,31,384,9),(2,64,189,256,9),(4,128,347,32,9)])) (.fork 3 (.leaf [(72,0,167,272,9),(68,0,313,130,9),(65,0,428,18,9)]) (.leaf [(264,0,231,16,9),(20,0,355,136,9),(1,16,486,8,9)]))))) (.fork 23 (.fork 11 (.fork 5 (.fork 2 (.leaf [(256,64,189,2,9),(260,0,187,64,8)]) (.leaf [(0,1,460,50,8),(258,64,189,0,8),(322,0,189,0,8)])) (.fork 3 (.leaf [(328,0,183,0,8),(336,0,175,0,8),(352,0,159,0,8)]) (.leaf [(36,128,347,0,8),(140,0,371,0,8),(257,0,190,64,8)]))) (.fork 6 (.fork 3 (.leaf [(67,0,428,16,8),(70,0,313,128,8),(134,0,377,0,8)]) (.leaf [(82,0,429,0,8),(0,256,23,232,8),(88,0,167,256,8)])) (.fork 3 (.leaf [(49,0,334,128,8),(40,0,471,0,8),(0,32,94,385,8)]) (.leaf [(416,0,95,0,8),(9,16,486,0,8),(224,0,31,256,8)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(194,0,313,4,8),(19,0,492,0,8)]) (.leaf [(5,0,504,2,8),(448,0,63,0,8),(28,0,355,128,8)])) (.fork 3 (.leaf [(34,0,349,128,8),(0,8,227,276,8),(0,4,305,202,8)]) (.leaf [(0,2,312,197,8),(8,4,353,146,7),(8,256,135,112,7)]))) (.fork 6 (.fork 3 (.leaf [(128,256,23,104,7),(128,4,305,74,7),(156,0,355,0,7)]) (.leaf [(193,0,318,0,7),(4,2,312,193,7),(256,8,163,84,7)])) (.fork 3 (.leaf [(256,32,78,145,7),(64,256,23,168,7),(64,32,30,385,7)]) (.leaf [(64,8,163,276,7),(64,2,312,133,7),(64,1,396,50,7)])))))) (.fork 46 (.fork 23 (.fork 11 (.fork 5 (.fork 2 (.leaf [(2,4,305,200,7),(2,1,332,176,7)]) (.leaf [(1,64,156,290,7),(1,32,30,448,7),(1,2,312,196,7)])) (.fork 3 (.leaf [(289,0,222,0,7),(32,256,23,200,7),(32,1,332,146,7)]) (.leaf [(324,0,187,0,7),(321,0,190,0,7),(296,0,215,0,7)]))) (.fork 6 (.fork 3 (.leaf [(268,0,243,0,7),(74,0,437,0,7),(35,0,476,0,7)]) (.leaf [(14,0,497,0,7),(7,0,504,0,7),(129,32,78,272,6)])) (.fork 3 (.leaf [(5,2,440,64,6),(130,1,332,48,6),(10,4,353,144,6)]) (.leaf [(136,4,369,2,6),(160,256,23,72,6),(388,0,27,96,6)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(96,256,23,136,6),(192,4,305,10,6)]) (.leaf [(384,8,99,20,6),(34,1,460,16,6),(66,1,396,48,6)])) (.fork 3 (.leaf [(33,16,454,8,6),(33,64,156,258,6),(96,1,396,18,6)]) (.leaf [(76,0,163,272,6),(160,1,332,18,6),(34,64,156,257,6)]))) (.fork 6 (.fork 3 (.leaf [(3,16,480,12,6),(72,256,23,160,6),(12,64,177,258,6)]) (.leaf [(257,32,78,144,6),(260,8,227,16,6),(260,64,185,2,6)])) (.fork 3 (.leaf [(260,128,27,96,6),(40,256,151,64,6),(65,2,312,132,6)]) (.leaf [(40,128,339,4,6),(320,32,30,129,6),(320,8,163,20,6)]))))) (.fork 23 (.fork 11 (.fork 5 (.fork 2 (.leaf [(98,1,396,16,5),(44,128,339,0,5)]) (.leaf [(388,8,99,16,5),(292,128,27,64,5),(321,32,30,128,5)])) (.fork 3 (.leaf [(452,0,27,32,5),(290,64,29,128,5),(324,8,163,16,5)]) (.leaf [(289,64,156,2,5),(7,128,344,32,5),(284,0,99,128,5)]))) (.fork 6 (.fork 3 (.leaf [(138,4,353,16,5),(142,0,369,0,5),(41,16,198,256,5)]) (.leaf [(27,0,480,4,5),(104,256,23,128,5),(268,64,177,2,5)])) (.fork 3 (.leaf [(29,0,480,2,5),(326,0,185,0,5),(396,0,99,16,5)]) (.leaf [(14,64,177,256,5),(332,0,179,0,5),(38,128,281,64,5)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(262,64,57,128,5),(163,0,348,0,5)]) (.leaf [(385,32,30,64,5),(193,2,312,4,5),(193,32,30,256,5)])) (.fork 3 (.leaf [(69,2,424,16,5),(35,128,344,4,5),(200,4,305,2,5)]) (.leaf [(35,64,156,256,5),(204,0,305,2,5),(74,4,305,128,5)]))) (.fork 6 (.fork 3 (.leaf [(78,0,177,256,5),(162,1,332,16,5),(172,0,339,0,5)]) (.leaf [(356,128,27,0,4),(197,2,312,0,4),(334,0,177,0,4)])) (.fork 3 (.leaf [(390,64,57,0,4),(31,0,480,0,4),(39,128,344,0,4)]) (.leaf [(449,32,30,0,4),(291,64,156,0,4),(484,0,27,0,4)])))))))
def comblevels : Nat → Packing
  | 8 => combl8
  | 9 => combl9
  | 10 => combl10
  | 11 => combl11
  | 12 => combl12
  | 13 => combl13
  | _ => emptyPacking
def combindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 1 9 1 4 (hashcombl9)
  | 10 => lookupWord 50 281 6 16 8 4 (hashcombl10)
  | 11 => lookupWord 835 4637 8 20 12 4 (hashcombl11)
  | 12 => lookupWord 829 4153 8 20 12 4 (hashcombl12)
  | 13 => lookupWord 62 431 5 16 8 4 (hashcombl13)
  | _ => fun _ => none
def comb : Forest := ⟨511,13,fun j => combsamples[j]?.getD (0,0),combcolumns,deadautos,comblevels,combindex⟩
set_option maxHeartbeats 0 in
theorem geomcomb : graphValid comb (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb8_0 : block comb 8 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allcomb8 : block comb 8 0 1=true := scomb8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb9_0 : block comb 9 0 64=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb9_64 : block comb 9 64 64=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb9_128 : block comb 9 128 21=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb9_149 : block comb 9 149 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allcomb9 : block comb 9 0 161=true := (@block_merge comb 9 0 149 12 (@block_merge comb 9 0 128 21 (@block_merge comb 9 0 64 64 scomb9_0 scomb9_64) scomb9_128) scomb9_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_0 : block comb 10 0 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_20 : block comb 10 20 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_84 : block comb 10 84 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_148 : block comb 10 148 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_212 : block comb 10 212 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_276 : block comb 10 276 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_340 : block comb 10 340 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_404 : block comb 10 404 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_468 : block comb 10 468 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_532 : block comb 10 532 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_596 : block comb 10 596 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_660 : block comb 10 660 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_724 : block comb 10 724 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_788 : block comb 10 788 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_852 : block comb 10 852 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_916 : block comb 10 916 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_980 : block comb 10 980 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1044 : block comb 10 1044 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1108 : block comb 10 1108 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1172 : block comb 10 1172 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1236 : block comb 10 1236 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1300 : block comb 10 1300 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1364 : block comb 10 1364 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1428 : block comb 10 1428 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1492 : block comb 10 1492 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1556 : block comb 10 1556 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1620 : block comb 10 1620 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1684 : block comb 10 1684 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1748 : block comb 10 1748 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1812 : block comb 10 1812 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1876 : block comb 10 1876 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_1940 : block comb 10 1940 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2004 : block comb 10 2004 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2068 : block comb 10 2068 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2132 : block comb 10 2132 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2196 : block comb 10 2196 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2260 : block comb 10 2260 45=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2305 : block comb 10 2305 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2369 : block comb 10 2369 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2433 : block comb 10 2433 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb10_2497 : block comb 10 2497 62=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allcomb10 : block comb 10 0 2559=true := (@block_merge comb 10 0 2497 62 (@block_merge comb 10 0 2433 64 (@block_merge comb 10 0 2369 64 (@block_merge comb 10 0 2305 64 (@block_merge comb 10 0 2260 45 (@block_merge comb 10 0 2196 64 (@block_merge comb 10 0 2132 64 (@block_merge comb 10 0 2068 64 (@block_merge comb 10 0 2004 64 (@block_merge comb 10 0 1940 64 (@block_merge comb 10 0 1876 64 (@block_merge comb 10 0 1812 64 (@block_merge comb 10 0 1748 64 (@block_merge comb 10 0 1684 64 (@block_merge comb 10 0 1620 64 (@block_merge comb 10 0 1556 64 (@block_merge comb 10 0 1492 64 (@block_merge comb 10 0 1428 64 (@block_merge comb 10 0 1364 64 (@block_merge comb 10 0 1300 64 (@block_merge comb 10 0 1236 64 (@block_merge comb 10 0 1172 64 (@block_merge comb 10 0 1108 64 (@block_merge comb 10 0 1044 64 (@block_merge comb 10 0 980 64 (@block_merge comb 10 0 916 64 (@block_merge comb 10 0 852 64 (@block_merge comb 10 0 788 64 (@block_merge comb 10 0 724 64 (@block_merge comb 10 0 660 64 (@block_merge comb 10 0 596 64 (@block_merge comb 10 0 532 64 (@block_merge comb 10 0 468 64 (@block_merge comb 10 0 404 64 (@block_merge comb 10 0 340 64 (@block_merge comb 10 0 276 64 (@block_merge comb 10 0 212 64 (@block_merge comb 10 0 148 64 (@block_merge comb 10 0 84 64 (@block_merge comb 10 0 20 64 scomb10_0 scomb10_20) scomb10_84) scomb10_148) scomb10_212) scomb10_276) scomb10_340) scomb10_404) scomb10_468) scomb10_532) scomb10_596) scomb10_660) scomb10_724) scomb10_788) scomb10_852) scomb10_916) scomb10_980) scomb10_1044) scomb10_1108) scomb10_1172) scomb10_1236) scomb10_1300) scomb10_1364) scomb10_1428) scomb10_1492) scomb10_1556) scomb10_1620) scomb10_1684) scomb10_1748) scomb10_1812) scomb10_1876) scomb10_1940) scomb10_2004) scomb10_2068) scomb10_2132) scomb10_2196) scomb10_2260) scomb10_2305) scomb10_2369) scomb10_2433) scomb10_2497)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_0 : block comb 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2 : block comb 11 2 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_66 : block comb 11 66 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_130 : block comb 11 130 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_194 : block comb 11 194 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_258 : block comb 11 258 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_322 : block comb 11 322 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_370 : block comb 11 370 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_434 : block comb 11 434 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_498 : block comb 11 498 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_562 : block comb 11 562 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_626 : block comb 11 626 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_690 : block comb 11 690 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_754 : block comb 11 754 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_818 : block comb 11 818 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_882 : block comb 11 882 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_946 : block comb 11 946 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1010 : block comb 11 1010 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1074 : block comb 11 1074 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1138 : block comb 11 1138 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1202 : block comb 11 1202 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1266 : block comb 11 1266 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1330 : block comb 11 1330 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1394 : block comb 11 1394 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1458 : block comb 11 1458 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1522 : block comb 11 1522 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1586 : block comb 11 1586 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1650 : block comb 11 1650 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1714 : block comb 11 1714 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1778 : block comb 11 1778 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1842 : block comb 11 1842 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1906 : block comb 11 1906 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_1970 : block comb 11 1970 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2034 : block comb 11 2034 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2098 : block comb 11 2098 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2162 : block comb 11 2162 43=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2205 : block comb 11 2205 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2269 : block comb 11 2269 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2333 : block comb 11 2333 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2397 : block comb 11 2397 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2461 : block comb 11 2461 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2525 : block comb 11 2525 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb11_2589 : block comb 11 2589 16=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allcomb11 : block comb 11 0 2605=true := (@block_merge comb 11 0 2589 16 (@block_merge comb 11 0 2525 64 (@block_merge comb 11 0 2461 64 (@block_merge comb 11 0 2397 64 (@block_merge comb 11 0 2333 64 (@block_merge comb 11 0 2269 64 (@block_merge comb 11 0 2205 64 (@block_merge comb 11 0 2162 43 (@block_merge comb 11 0 2098 64 (@block_merge comb 11 0 2034 64 (@block_merge comb 11 0 1970 64 (@block_merge comb 11 0 1906 64 (@block_merge comb 11 0 1842 64 (@block_merge comb 11 0 1778 64 (@block_merge comb 11 0 1714 64 (@block_merge comb 11 0 1650 64 (@block_merge comb 11 0 1586 64 (@block_merge comb 11 0 1522 64 (@block_merge comb 11 0 1458 64 (@block_merge comb 11 0 1394 64 (@block_merge comb 11 0 1330 64 (@block_merge comb 11 0 1266 64 (@block_merge comb 11 0 1202 64 (@block_merge comb 11 0 1138 64 (@block_merge comb 11 0 1074 64 (@block_merge comb 11 0 1010 64 (@block_merge comb 11 0 946 64 (@block_merge comb 11 0 882 64 (@block_merge comb 11 0 818 64 (@block_merge comb 11 0 754 64 (@block_merge comb 11 0 690 64 (@block_merge comb 11 0 626 64 (@block_merge comb 11 0 562 64 (@block_merge comb 11 0 498 64 (@block_merge comb 11 0 434 64 (@block_merge comb 11 0 370 64 (@block_merge comb 11 0 322 48 (@block_merge comb 11 0 258 64 (@block_merge comb 11 0 194 64 (@block_merge comb 11 0 130 64 (@block_merge comb 11 0 66 64 (@block_merge comb 11 0 2 64 scomb11_0 scomb11_2) scomb11_66) scomb11_130) scomb11_194) scomb11_258) scomb11_322) scomb11_370) scomb11_434) scomb11_498) scomb11_562) scomb11_626) scomb11_690) scomb11_754) scomb11_818) scomb11_882) scomb11_946) scomb11_1010) scomb11_1074) scomb11_1138) scomb11_1202) scomb11_1266) scomb11_1330) scomb11_1394) scomb11_1458) scomb11_1522) scomb11_1586) scomb11_1650) scomb11_1714) scomb11_1778) scomb11_1842) scomb11_1906) scomb11_1970) scomb11_2034) scomb11_2098) scomb11_2162) scomb11_2205) scomb11_2269) scomb11_2333) scomb11_2397) scomb11_2461) scomb11_2525) scomb11_2589)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb12_0 : block comb 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb12_36 : block comb 12 36 64=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb12_100 : block comb 12 100 46=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb12_146 : block comb 12 146 53=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allcomb12 : block comb 12 0 199=true := (@block_merge comb 12 0 146 53 (@block_merge comb 12 0 100 46 (@block_merge comb 12 0 36 64 scomb12_0 scomb12_36) scomb12_100) scomb12_146)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb13_0 : block comb 13 0 2=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem scomb13_2 : block comb 13 2 2=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allcomb13 : block comb 13 0 4=true := (@block_merge comb 13 0 2 2 scomb13_0 scomb13_2)
theorem tablescomb : checkedTables comb 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block comb 0 0 0 = true)
  · exact (rfl : block comb 1 0 0 = true)
  · exact (rfl : block comb 2 0 0 = true)
  · exact (rfl : block comb 3 0 0 = true)
  · exact (rfl : block comb 4 0 0 = true)
  · exact (rfl : block comb 5 0 0 = true)
  · exact (rfl : block comb 6 0 0 = true)
  · exact (rfl : block comb 7 0 0 = true)
  · exact allcomb8
  · exact allcomb9
  · exact allcomb10
  · exact allcomb11
  · exact allcomb12
  · exact allcomb13

def w0 : Sig := neg (inputs.getD 0 zero)
def wA : Sig := bin true (inputs.getD 2 zero) (inputs.getD 3 zero)
def wB : Sig := bin true (inputs.getD 2 zero) (inputs.getD 8 zero)
def wC : Sig := bin true (inputs.getD 8 zero) (inputs.getD 3 zero)

def deadRoots : List Sig := inputs
def a1Roots : List Sig := inputs ++ [w0, wA]
def a2Roots : List Sig := inputs.tail ++ [w0, wA]
def b1Roots : List Sig := inputs ++ [w0, wB]
def b2Roots : List Sig := inputs.tail ++ [w0, wB]

theorem dead_impossible : Impossible graph 14 inputs.toFinset :=
  dead_start (before_sound known383 valid383) geomdead tablesdead

theorem comb_impossible : ∀ i < (comb.levels 13).1,
    Impossible graph 13 (stateSet comb 13 i).toFinset := by
  have h := forest_all comb 13 (boundsBefore known383) (before_sound known383 valid383)
    geomcomb tablescomb 13 (le_refl _)
  have tgt : targetOf comb = graph := by decide +kernel
  intro i hi
  exact tgt ▸ h i hi

theorem dead_ess : ∀ a ∈ inputs, Essential graph inputs a := by
  intro a ha
  have hm : ∃ i : Fin 9, a = inputs.getD i.val zero := by
    rw [← input_list] at ha
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
    exact ⟨i, hi.symm⟩
  obtain ⟨i, rfl⟩ := hm
  have cut := seed_witness i
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at cut
  exact ⟨absentRow i, presentRow i, cut.1, fun v hv hne =>
    (cut.2 v (List.mem_append_left _ hv)).resolve_left hne⟩

theorem dead_sub {k t S} (hk : k ≤ 14) (h : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ inputs) : False := by
  have eqS : inputs.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun ha => ?_, sub a⟩
    obtain ⟨r, s, hd, iso⟩ := dead_ess a ha
    exact raw_required h inputs a sub r s hd iso
  exact dead_impossible k t hk (eqS.symm ▸ h)

def pairA (i : Fin 8) : Row × Row :=
  let v := i.val + 1
  let nb := [2, 1, 2, 3, 0, 1, 2, 3].getD i.val 0
  let r0 := if v = 2 then (1 <<< nb) ||| (1 <<< 3)
            else if v = 3 then (1 <<< nb) ||| (1 <<< 2)
            else (1 <<< nb)
  (Fin.ofNat 512 r0, Fin.ofNat 512 (r0 ||| (1 <<< v)))

def pairB (i : Fin 8) : Row × Row :=
  let v := i.val + 1
  let nb := [2, 1, 2, 3, 0, 1, 2, 5].getD i.val 0
  let r0 := if v = 2 then (1 <<< nb) ||| (1 <<< 8)
            else if v = 8 then (1 <<< nb) ||| (1 <<< 2)
            else (1 <<< nb)
  (Fin.ofNat 512 r0, Fin.ofNat 512 (r0 ||| (1 <<< v)))

theorem essA_check : ∀ i : Fin 8,
    witnessB graph a1Roots (inputs.getD (i.val + 1) zero) (pairA i) = true := by
  decide +kernel

theorem essB_check : ∀ i : Fin 8,
    witnessB graph b1Roots (inputs.getD (i.val + 1) zero) (pairB i) = true := by
  decide +kernel

theorem a2_set : (stateSet comb 13 0).toFinset = a2Roots.toFinset := by
  apply sameWords_sound
  decide +kernel

theorem b2_set : (stateSet comb 13 1).toFinset = b2Roots.toFinset := by
  apply sameWords_sound
  decide +kernel

theorem a1_set : (stateSet comb 13 2).toFinset = a1Roots.toFinset := by
  apply sameWords_sound
  decide +kernel

theorem b1_set : (stateSet comb 13 3).toFinset = b1Roots.toFinset := by
  apply sameWords_sound
  decide +kernel

theorem comb_root_count : 4 ≤ (comb.levels 13).1 := by decide +kernel

private lemma getD_mem_lt {α : Type} (l : List α) (i : Nat) (d : α) (hi : i < l.length) :
    l.getD i d ∈ l := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

private theorem tail_mem_nz : ∀ j : Fin 9, j.val ≠ 0 → inputs.getD j.val zero ∈ inputs.tail := by
  decide +kernel

theorem caseA_impossible {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ a1Roots) : False := by
  by_cases ha : wA ∈ S
  · by_cases h0 : w0 ∈ S
    · have req (i : Fin 8) : inputs.getD (i.val + 1) zero ∈ S := by
        obtain ⟨r, s, hd, iso⟩ := witnessB_sound (essA_check i)
        exact raw_required h a1Roots _ sub r s hd iso
      by_cases hx0 : inputs.getD 0 zero ∈ S
      · have eqS : a1Roots.toFinset = S := by
          ext v
          rw [List.mem_toFinset]
          refine ⟨fun hv => ?_, sub v⟩
          simp only [a1Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with h_in | (rfl | rfl)
          · rw [← input_list, List.mem_ofFn] at h_in
            obtain ⟨j, rfl⟩ := h_in
            rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
            · simpa [hj0] using hx0
            · simpa [Nat.sub_add_cancel hjpos] using req ⟨j.val - 1, by omega⟩
          · exact h0
          · exact ha
        rw [← a1_set] at eqS
        exact comb_impossible 2 (lt_of_lt_of_le (by decide) comb_root_count) k t hk (eqS.symm ▸ h)
      · have eqS : a2Roots.toFinset = S := by
          ext v
          rw [List.mem_toFinset]
          refine ⟨fun hv => ?_, fun hv => ?_⟩
          · simp only [a2Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with h_in | (rfl | rfl)
            · have hi : v ∈ inputs := List.mem_of_mem_tail h_in
              rw [← input_list, List.mem_ofFn] at hi
              obtain ⟨j, rfl⟩ := hi
              by_cases hj0 : j.val = 0
              · have h0in : inputs.getD 0 zero ∈ inputs.tail := by simpa [hj0] using h_in
                have absurd0 : inputs.getD 0 zero ∉ inputs.tail := by decide +kernel
                exact False.elim (absurd0 h0in)
              · have hjpos : 0 < j.val := by omega
                simpa [Nat.sub_add_cancel hjpos] using req ⟨j.val - 1, by omega⟩
            · exact h0
            · exact ha
          · have hv1 := sub v hv
            simp only [a1Roots, a2Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv1 ⊢
            rcases hv1 with h_in | rfl | rfl
            · left
              rw [← input_list, List.mem_ofFn] at h_in
              obtain ⟨j, rfl⟩ := h_in
              by_cases hj0 : j.val = 0
              · exact False.elim (hx0 (by simpa [hj0] using hv))
              · exact tail_mem_nz j hj0
            · right; left; rfl
            · right; right; rfl
        rw [← a2_set] at eqS
        exact comb_impossible 0 (lt_of_lt_of_le (by decide) comb_root_count) k t hk (eqS.symm ▸ h)
    · have sub' : ∀ v ∈ S, v ∈ wA :: inputs := by
        intro v hv
        have hv1 := sub v hv
        simp only [a1Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv1
        rcases hv1 with h_in | rfl | rfl
        · exact List.mem_cons_of_mem _ h_in
        · exact False.elim (h0 hv)
        · exact List.mem_cons_self
      have repA : witness inputs wA := Or.inr ⟨true, inputs.getD 2 zero, inputs.getD 3 zero,
        getD_mem_lt _ _ _ (by decide), getD_mem_lt _ _ _ (by decide),
        by unfold proper; decide +kernel, by unfold proper; decide +kernel, by decide +kernel, rfl⟩
      obtain ⟨k', t', S', hk', h', sub''⟩ := pull_cons h (Or.inr repA) sub'
      exact dead_sub (by omega) h' sub''
  · have sub' : ∀ v ∈ S, v ∈ w0 :: inputs := by
      intro v hv
      have hv1 := sub v hv
      simp only [a1Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv1
      rcases hv1 with h_in | rfl | rfl
      · exact List.mem_cons_of_mem _ h_in
      · exact List.mem_cons_self
      · exact False.elim (ha hv)
    have rep0 : witness inputs w0 := Or.inl ⟨inputs.getD 0 zero,
      getD_mem_lt _ _ _ (by decide), by unfold proper; decide +kernel, rfl⟩
    obtain ⟨k', t', S', hk', h', sub''⟩ := pull_cons h (Or.inr rep0) sub'
    exact dead_sub (by omega) h' sub''

theorem caseB_impossible {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ b1Roots) : False := by
  by_cases hb : wB ∈ S
  · by_cases h0 : w0 ∈ S
    · have req (i : Fin 8) : inputs.getD (i.val + 1) zero ∈ S := by
        obtain ⟨r, s, hd, iso⟩ := witnessB_sound (essB_check i)
        exact raw_required h b1Roots _ sub r s hd iso
      by_cases hx0 : inputs.getD 0 zero ∈ S
      · have eqS : b1Roots.toFinset = S := by
          ext v
          rw [List.mem_toFinset]
          refine ⟨fun hv => ?_, sub v⟩
          simp only [b1Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with h_in | (rfl | rfl)
          · rw [← input_list, List.mem_ofFn] at h_in
            obtain ⟨j, rfl⟩ := h_in
            rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
            · simpa [hj0] using hx0
            · simpa [Nat.sub_add_cancel hjpos] using req ⟨j.val - 1, by omega⟩
          · exact h0
          · exact hb
        rw [← b1_set] at eqS
        exact comb_impossible 3 (lt_of_lt_of_le (by decide) comb_root_count) k t hk (eqS.symm ▸ h)
      · have eqS : b2Roots.toFinset = S := by
          ext v
          rw [List.mem_toFinset]
          refine ⟨fun hv => ?_, fun hv => ?_⟩
          · simp only [b2Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with h_in | (rfl | rfl)
            · have hi : v ∈ inputs := List.mem_of_mem_tail h_in
              rw [← input_list, List.mem_ofFn] at hi
              obtain ⟨j, rfl⟩ := hi
              by_cases hj0 : j.val = 0
              · have h0in : inputs.getD 0 zero ∈ inputs.tail := by simpa [hj0] using h_in
                have absurd0 : inputs.getD 0 zero ∉ inputs.tail := by decide +kernel
                exact False.elim (absurd0 h0in)
              · have hjpos : 0 < j.val := by omega
                simpa [Nat.sub_add_cancel hjpos] using req ⟨j.val - 1, by omega⟩
            · exact h0
            · exact hb
          · have hv1 := sub v hv
            simp only [b1Roots, b2Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv1 ⊢
            rcases hv1 with h_in | rfl | rfl
            · left
              rw [← input_list, List.mem_ofFn] at h_in
              obtain ⟨j, rfl⟩ := h_in
              by_cases hj0 : j.val = 0
              · exact False.elim (hx0 (by simpa [hj0] using hv))
              · exact tail_mem_nz j hj0
            · right; left; rfl
            · right; right; rfl
        rw [← b2_set] at eqS
        exact comb_impossible 1 (lt_of_lt_of_le (by decide) comb_root_count) k t hk (eqS.symm ▸ h)
    · have sub' : ∀ v ∈ S, v ∈ wB :: inputs := by
        intro v hv
        have hv1 := sub v hv
        simp only [b1Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv1
        rcases hv1 with h_in | rfl | rfl
        · exact List.mem_cons_of_mem _ h_in
        · exact False.elim (h0 hv)
        · exact List.mem_cons_self
      have repB : witness inputs wB := Or.inr ⟨true, inputs.getD 2 zero, inputs.getD 8 zero,
        getD_mem_lt _ _ _ (by decide), getD_mem_lt _ _ _ (by decide),
        by unfold proper; decide +kernel, by unfold proper; decide +kernel, by decide +kernel, rfl⟩
      obtain ⟨k', t', S', hk', h', sub''⟩ := pull_cons h (Or.inr repB) sub'
      exact dead_sub (by omega) h' sub''
  · have sub' : ∀ v ∈ S, v ∈ w0 :: inputs := by
      intro v hv
      have hv1 := sub v hv
      simp only [b1Roots, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv1
      rcases hv1 with h_in | rfl | rfl
      · exact List.mem_cons_of_mem _ h_in
      · exact List.mem_cons_self
      · exact False.elim (hb hv)
    have rep0 : witness inputs w0 := Or.inl ⟨inputs.getD 0 zero,
      getD_mem_lt _ _ _ (by decide), by unfold proper; decide +kernel, rfl⟩
    obtain ⟨k', t', S', hk', h', sub''⟩ := pull_cons h (Or.inr rep0) sub'
    exact dead_sub (by omega) h' sub''

def sigmaMoves : List Move := ([118, 130, 81] : List Nat).map swapRows

theorem sigma_ok : autoOK graph sigmaMoves = true := by decide +kernel
theorem sigma_w0 : movedWord sigmaMoves w0 = w0 := by decide +kernel
theorem sigma_wC : movedWord sigmaMoves wC = wA := by decide +kernel
theorem sigma_inputs : inputs.all (fun a => a1Roots.contains (movedWord sigmaMoves a)) = true := by decide +kernel

theorem caseC_impossible {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (sub : ∀ v ∈ S, v ∈ inputs ++ [w0, wC]) : False := by
  have ok := sigma_ok
  simp only [autoOK, Bool.and_eq_true, beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow sigmaMoves) :=
    fun r => ⟨movedRow sigmaMoves.reverse r, composed_id ok.2 r⟩
  have run := live_rename h (movedRow sigmaMoves) onto
  have goal : rename (movedRow sigmaMoves) graph = graph :=
    (moved_eq_rename sigmaMoves graph).symm.trans ok.1.1
  rw [goal] at run
  apply caseA_impossible hk run
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  rw [← moved_eq_rename]
  have hu' := sub u hu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu'
  rcases hu' with h_in | rfl | rfl
  · have ha := List.all_eq_true.mp sigma_inputs u h_in
    simpa only [List.contains_eq_mem, decide_eq_true_eq] using ha
  · rw [sigma_w0]
    simp [a1Roots]
  · rw [sigma_wC]
    simp [a1Roots]

theorem caseDup_impossible {k t S} (hk : k ≤ 13) (h : Live graph k t S) (a : Nat) (ha : a < 9)
    (sub : ∀ v ∈ S, v ∈ inputs ++ [w0, inputs.getD a zero]) : False := by
  have hmem : inputs.getD a zero ∈ inputs := getD_mem_lt _ _ _ (by simpa [inputs] using ha)
  have sub' : ∀ v ∈ S, v ∈ w0 :: inputs := by
    intro v hv
    have hv1 := sub v hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv1
    rcases hv1 with hin | rfl | rfl
    · exact List.mem_cons_of_mem _ hin
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hmem
  have rep0 : witness inputs w0 := Or.inl ⟨inputs.getD 0 zero,
    getD_mem_lt _ _ _ (by decide), by unfold proper; decide +kernel, rfl⟩
  obtain ⟨k', t', S', hk', h', sub''⟩ := pull_cons h (Or.inr rep0) sub'
  exact dead_sub (by omega) h' sub''

theorem suffix_extract (a b : Nat) (ha : a < 9) (hb : b < 9)
    (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsz : C.size ≤ 13)
    (he : ∀ x8 : Fin 9 → Bool,
      have x9 : List Bool := List.ofFn x8 ++ [!x8 0];
      C.eval (x9 ++ [GateOp.or.eval [x9.getD a false, x9.getD b false]]) = edge x8) :
    ∃ k t S, k ≤ 13 ∧ Live graph k t S ∧
      ∀ v ∈ S, v ∈ inputs ++ [w0, bin true (inputs.getD a zero) (inputs.getD b zero)] := by
  let wAB := bin true (inputs.getD a zero) (inputs.getD b zero)
  let roots := inputs ++ [w0, wAB]
  have hinit (r : Row) : roots.map (bit r) =
      (List.ofFn (sample r) ++ [!sample r 0]) ++
      [GateOp.or.eval [(List.ofFn (sample r) ++ [!sample r 0]).getD a false,
                       (List.ofFn (sample r) ++ [!sample r 0]).getD b false]] := by
    have bw0 : bit r w0 = !sample r 0 := by
      rw [w0, bit_neg]; rfl
    have ba : (List.ofFn (sample r) ++ [!sample r 0]).getD a false = bit r (inputs.getD a zero) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [ha]), List.getElem?_ofFn]
      simp [ha, sample]
    have bb : (List.ofFn (sample r) ++ [!sample r 0]).getD b false = bit r (inputs.getD b zero) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hb]), List.getElem?_ofFn]
      simp [hb, sample]
    have bwAB : bit r wAB = GateOp.or.eval [bit r (inputs.getD a zero), bit r (inputs.getD b zero)] := by
      dsimp only [wAB]; rw [bit_bin]; simp [GateOp.eval]
    rw [ba, bb]
    simp only [roots, List.map_append, List.map_cons, List.map_nil, sampled, bw0, bwAB, List.append_assoc, List.cons_append, List.nil_append]
  have goalEq : (execute C.gates roots).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    change bit r ((execute C.gates roots).getD C.output zero) = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (hfan g hg).1), hinit r]
    change C.eval _ = bit r graph
    exact (he (sample r)).trans (edge_table r).symm
  have out := get_rep (execute C.gates roots) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, t, S, hk, run, sub⟩ := extract C.gates roots hfan graph_proper targetIn
  exact ⟨k, t, S, hk.trans hsz, run, sub⟩

end PEqualNP.Outside.L_meta_3172

open PEqualNP.Outside.L_meta_3172 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_3172 : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen _ h238 C hfan hsz
  by_contra! he
  rcases x1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · have ha : a = 2 ∨ a = 3 ∨ a = 8 := h238 a (by simp)
    have hb : b = 2 ∨ b = 3 ∨ b = 8 := h238 b (by simp)
    have ha9 : a < 9 := by omega
    have hb9 : b < 9 := by omega
    obtain ⟨k, t, S, hk, run, sub⟩ := suffix_extract a b ha9 hb9 C hfan hsz (fun x8 => by
      simpa only [edge, List.map_cons, List.map_nil] using Classical.not_not.mp (he x8))
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · refine caseDup_impossible hk run 2 (by decide) ?_
      intro v hv
      have := sub v hv
      simpa only [(bin_laws _).2.2.2.2.2] using this
    · exact caseA_impossible hk run sub
    · exact caseB_impossible hk run sub
    · refine caseA_impossible hk run ?_
      intro v hv
      have := sub v hv
      simpa only [a1Roots, wA, bin_comm true] using this
    · refine caseDup_impossible hk run 3 (by decide) ?_
      intro v hv
      have := sub v hv
      simpa only [(bin_laws _).2.2.2.2.2] using this
    · refine caseC_impossible hk run ?_
      intro v hv
      have := sub v hv
      simpa only [wC, bin_comm true] using this
    · refine caseB_impossible hk run ?_
      intro v hv
      have := sub v hv
      simpa only [b1Roots, wB, bin_comm true] using this
    · exact caseC_impossible hk run sub
    · refine caseDup_impossible hk run 8 (by decide) ?_
      intro v hv
      have := sub v hv
      simpa only [(bin_laws _).2.2.2.2.2] using this
  · simp at hlen
