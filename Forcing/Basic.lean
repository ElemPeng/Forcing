axiom Set : Type
axiom zfmem : Set → Set → Prop

instance : Membership Set Set where mem x y := zfmem y x

axiom exist : Nonempty Set

@[ext] axiom zfexf (x y : Set) : (∀ s, s ∈ x ↔ s ∈ y) → x = y
axiom pair (x y : Set) : ∃ s : Set, ∀ z, (z ∈ s ↔ z = x ∨ z = y)

noncomputable def Dbl (x y : Set) := Exists.choose <| pair x y

noncomputable def Sngl (x : Set) := Dbl x x

theorem pair_mem_iff {x y z : Set} : z ∈ Dbl x y ↔ z = x ∨ z = y :=
    ((Exists.choose_spec <| pair x y) z)

theorem pair_mem_left {x y : Set} : x ∈ Dbl x y :=
    pair_mem_iff.mpr <| Or.inl rfl

theorem pair_mem_right {x y : Set} : y ∈ Dbl x y :=
    pair_mem_iff.mpr <| Or.inr rfl

theorem sngl_mem_iff {x y: Set} : y ∈ Sngl x ↔ y = x := by
    have h := ((Exists.choose_spec <| pair x x) y)
    unfold Sngl Dbl; simpa using h

theorem sngl_mem {x : Set} : x ∈ Sngl x :=
    (((Exists.choose_spec <| pair x x)) x).mpr <| Or.inl rfl

axiom union (s : Set) : ∃ u : Set, ∀ x, (x ∈ u ↔ ∃ a : Set, x ∈ a ∧ a ∈ s)

noncomputable def ZFU (s : Set) := Exists.choose <| union s

prefix:80 "⋃" => ZFU -- \bigcup

theorem union_mem_iff {s a : Set} : a ∈ ⋃s ↔ ∃ x, a ∈ x ∧ x ∈ s :=
    (Exists.choose_spec <| union s) a

theorem union_mem_of_mem_of_mem {s a x : Set} : a ∈ x → x ∈ s → a ∈ ⋃s :=
    fun hax hxs ↦ union_mem_iff.mpr ⟨x, hax, hxs⟩

instance : HasSubset Set where Subset := fun x y ↦ ∀ a : Set, (a ∈ x → a ∈ y)
instance : HasSSubset Set where SSubset := fun x y ↦ x ⊆ y ∧ x ≠ y

example {s : Set} : s ⊆ s := fun _ hx ↦ hx
example {s : Set} : ¬ (s ⊂ s) := fun ⟨_, h⟩ ↦ h rfl

theorem eq_of_subset_of_subset (a b : Set) : a ⊆ b → b ⊆ a → a = b := by
    intro h1 h2; ext z; exact Iff.intro (fun h ↦ h1 z h) (fun h ↦ h2 z h)

/- sigh, going to do separation axiom honestly-/

inductive Wff where
    | mem : Nat → Nat → Wff
    | eq : Nat → Nat → Wff
    | not : Wff → Wff
    | imp : Wff → Wff → Wff
    | all : Nat → Wff → Wff

structure Model where
    M : Type
    E : M → M → Prop

theorem not_iff_comm (p q : Prop) : (¬p ↔ q) ↔ (¬ q ↔ p) := by
    conv => lhs; rw [←Classical.not_iff, Iff.comm, Classical.not_iff]

abbrev Assign (ℳ : Model) := Nat → ℳ.M

def AgreeOff {ℳ : Model} (i : Nat) (σ τ : Assign ℳ) := ∀ j : Nat, i ≠ j → σ j = τ j

@[symm] theorem AgreeOff.symm {ℳ : Model} {i : Nat} {σ τ : Assign ℳ} (h : AgreeOff i σ τ) : AgreeOff i τ σ := by
    unfold AgreeOff at h ⊢; simpa [Eq.comm]

theorem eq_of_agree_off {ℳ : Model} {i j : Nat} {σ τ : Assign ℳ} :
    AgreeOff i σ τ → i ≠ j → σ j = τ j := fun h1 h2 ↦ h1 j h2

theorem eq_of_agree_off' {ℳ : Model} {i j : Nat} {σ τ : Assign ℳ} (m : ℳ.M) :
    AgreeOff i σ τ → i ≠ j → σ j = m → τ j = m := by
    intro h1 h2 h3; rw [←h3]; symm; exact eq_of_agree_off h1 h2

theorem agree_off_triv {ℳ : Model} {i : Nat} {σ : Assign ℳ} :
    AgreeOff i σ σ := fun _ _ ↦ rfl

def Sat {ℳ : Model} (σ : Assign ℳ) : Wff → Prop
    | Wff.mem i j => ℳ.E (σ i) (σ j)
    | Wff.eq i j => (σ i) = (σ j)
    | Wff.not φ => ¬(Sat σ φ)
    | Wff.imp φ ψ => (Sat σ φ) → (Sat σ ψ)
    | Wff.all i φ => ∀ τ : Assign ℳ, AgreeOff i σ τ → (Sat τ φ)

def Wff.or (φ ψ : Wff) := φ.not.imp ψ

def Wff.and (φ ψ : Wff) := (φ.imp ψ.not).not

def Wff.iff (φ ψ : Wff) := (φ.imp ψ).and (ψ.imp φ)

def Wff.some (i : Nat) (φ : Wff) : Wff := (φ.not.all i).not

@[simp] theorem Wff.mem_iff {ℳ : Model} {σ : Assign ℳ} {i j : Nat} :
    Sat σ (mem i j) ↔ ℳ.E (σ i) (σ j) := by rfl

@[simp] theorem Wff.eq_iff {ℳ : Model} {σ : Assign ℳ} {i j : Nat} :
    Sat σ (eq i j) ↔ (σ i) = (σ j) := by rfl

@[simp] theorem Wff.not_iff {ℳ : Model} {σ : Assign ℳ} {φ : Wff} :
    Sat σ φ.not ↔ ¬(Sat σ φ) := by rfl

@[simp] theorem Wff.imp_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ: Wff} :
    Sat σ (φ.imp ψ) ↔ (Sat σ φ) → (Sat σ ψ) := by rfl

@[simp] theorem Wff.all_iff {ℳ : Model} {σ : Assign ℳ} {i : Nat} {φ : Wff} :
    Sat σ (φ.all i) ↔ ∀ τ : Assign ℳ, AgreeOff i σ τ → (Sat τ φ) := by rfl

@[simp] theorem Wff.or_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ : Wff} :
    Sat σ (φ.or ψ) ↔ (Sat σ φ) ∨ (Sat σ ψ) := by
    unfold Wff.or; rw [Classical.or_iff_not_imp_left]; rfl

@[simp] theorem Wff.and_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ : Wff} :
    Sat σ (φ.and ψ) ↔ (Sat σ φ) ∧ (Sat σ ψ) := by
    unfold Wff.and; change ¬ (Sat σ (φ.imp ψ.not)) ↔ Sat σ φ ∧ Sat σ ψ
    rw [not_iff_comm, not_and, Wff.imp_iff, not_iff]

@[simp] theorem Wff.iff_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ : Wff} :
    Sat σ (φ.iff ψ) ↔ ((Sat σ φ) ↔ (Sat σ ψ)) := by
    unfold iff; rw [and_iff, imp_iff, imp_iff,
        iff_iff_implies_and_implies (a := Sat σ φ)]

@[simp] theorem Wff.some_iff {ℳ : Model} {σ : Assign ℳ} {i : Nat} {φ : Wff} :
    Sat σ (φ.some i) ↔ ∃ τ : Assign ℳ, AgreeOff i σ τ ∧ (Sat τ φ) := by
    unfold some; rw [not_iff, not_iff_comm, not_exists];
    simp [not_and, all_iff, not_iff]

def update {ℳ : Model} : Assign ℳ → Nat → ℳ.M → Assign ℳ :=
    fun σ v a j ↦ if v = j then a else σ j

theorem update_same {ℳ : Model} {σ : Assign ℳ} {v : Nat} {a : ℳ.M} :
    update σ v a v = a := by unfold update; rw [ite_eq_left rfl]

theorem update_other {ℳ : Model} {σ : Assign ℳ} {v n : Nat} {a : ℳ.M} :
    v ≠ n → update σ v a n = σ n := by
    intro hne; unfold update; rw [ite_eq_right hne]

theorem update_agree_off {ℳ : Model} {σ : Assign ℳ} {v : Nat} {a : ℳ.M} :
    AgreeOff v σ (update σ v a) := fun _ hn ↦ (update_other hn).symm

theorem update_agree_off' {ℳ : Model} {σ : Assign ℳ} {v : Nat} {a : ℳ.M} :
    AgreeOff v (update σ v a) σ := fun _ hn ↦ (update_other hn)

abbrev ZF : Model := ⟨Set, (· ∈ ·) ⟩

def Wff.eval {ℳ : Model} (σ : Assign ℳ) (φ : Wff) (v : Nat) (a : ℳ.M) :=
    Sat (update σ v a) φ

--- Defining predicates so I don't have to use this Wff stuff
def Pred := Assign ZF → Prop

def Definable (P : Pred) := ∃ φ : Wff, ∀ σ : Assign ZF, Sat σ φ ↔ P σ

theorem mem_definable (i j : Nat) : Definable (fun σ ↦ σ i ∈ σ j) := by --- This says x_i ∈ x_j
    exact ⟨Wff.mem i j, by simp⟩

theorem eq_definable (i j : Nat) : Definable (fun σ ↦ σ i = σ j) := by
    exact ⟨Wff.eq i j, by simp⟩

@[simp] def Pred.not (P : Pred) : Pred := fun σ ↦ ¬ (P σ)

theorem not_definable (P : Pred) (hP : Definable P) : Definable (P.not) := by
    obtain ⟨φ, hφ⟩ := hP; exact ⟨φ.not, by simp_all⟩

@[simp] def Pred.or (P Q : Pred) : Pred := fun σ ↦ (P σ) ∨ (Q σ)

theorem or_definable (P Q : Pred) (hP : Definable P) (hQ : Definable Q) : Definable (P.or Q) := by
    obtain ⟨φ, hφ⟩ := hP; obtain ⟨ψ, hψ⟩ := hQ
    exact ⟨φ.or ψ, by simp_all⟩

@[simp] def Pred.imp (P Q : Pred) : Pred := fun σ ↦ (P σ) → (Q σ)

theorem imp_definable (P Q : Pred) (hP : Definable P) (hQ : Definable Q) : Definable (P.imp Q) := by
    obtain ⟨φ, hφ⟩ := hP; obtain ⟨ψ, hψ⟩ := hQ
    exact ⟨φ.imp ψ, by simp_all⟩

--- defining a ⊆ b
def is_subset_wff (a b x : Nat) (_hdist : [a, b, x].Nodup := by decide) : Wff :=
    ((Wff.mem x a).imp (Wff.mem x b)).all x

theorem Wff.is_subset_iff {σ : Assign ZF} (a b x : Nat) (hdist : [a, b, x].Nodup) :
    Sat σ (is_subset_wff a b x hdist) ↔ σ a ⊆ σ b := by
    have hxa : x ≠ a := by grind
    have hxb : x ≠ b := by grind
    simp [is_subset_wff]; constructor
    ·   intro hL s hs; have hL2 := hL (update σ x s) update_agree_off
        simp [update_same, update_other hxa, update_other hxb] at hL2
        exact hL2 hs
    ·   intro hτab τ hτ hσxa; rw [eq_of_agree_off hτ hxa, eq_of_agree_off hτ hxb] at hτab
        exact hτab (τ x) hσxa

axiom separ_scheme (φ : Wff) (σ : Assign ZF) (x : Set) : ∃ y : Set, ∀ a,
(a ∈ y ↔ a ∈ x ∧ φ.eval σ 0 a)

noncomputable def Separ (φ : Wff) (σ : Assign ZF) (x : Set)  := Exists.choose (separ_scheme φ σ x)

theorem separ_is_subset {φ : Wff} {σ : Assign ZF} {x : Set}  : Separ φ σ x ⊆ x :=
    fun a ha ↦ ((Exists.choose_spec (separ_scheme φ σ x) a).mp ha).1

theorem separ_has_prop {φ : Wff} {σ : Assign ZF} {x a : Set} : a ∈ Separ φ σ x → φ.eval σ 0 a :=
    fun ha ↦ ((Exists.choose_spec (separ_scheme φ σ x) a).mp ha).2

theorem separ_mem_iff {φ : Wff} {σ : Assign ZF} {x a : Set} : a ∈ Separ φ σ x ↔ (a ∈ x ∧ φ.eval σ 0 a) :=
    Exists.choose_spec (separ_scheme φ σ x) a



def const_param (x : Set) : Assign ZF := fun _ ↦ x

theorem const_param_eq {x : Set} {i : Nat} : const_param x i = x := by rfl

theorem exists_empty : ∃ s : Set, ∀ a : Set, a ∉ s := by
    have ⟨x⟩ := exist; refine ⟨Separ (Wff.eq 0 0).not (const_param x) x, ?_⟩
    intro a ha; rw [separ_mem_iff] at ha; have ⟨_, ha'⟩ := ha;
    unfold Wff.eval update Sat Sat at ha'
    simp at ha'

noncomputable def ZFempty : Set := Exists.choose exists_empty

noncomputable instance : EmptyCollection Set where emptyCollection := ZFempty

noncomputable def one_param (i : Nat) (x : Set) := update (const_param ∅) i x

theorem one_param_same (i: Nat) (x : Set) : one_param i x i = x := by
    unfold one_param; exact update_same

theorem not_mem_empty (s : Set) : s ∉ (∅ : Set) := (Exists.choose_spec exists_empty) s

def Set.IsEmpty (s : Set) := ∀ x : Set, x ∉ s
def Set.Nonempty (s : Set) := ∃ x : Set, x ∈ s

theorem eq_iff_isEmpty {s : Set} : s = ∅ ↔ s.IsEmpty := by
    constructor
    ·   intro h; subst h; exact not_mem_empty
    ·   intro hs; ext z; simp [hs z, not_mem_empty z]

theorem isEmpty_iff_eq {s : Set} : s.IsEmpty ↔ s = ∅ := eq_iff_isEmpty.symm

theorem not_nonempty_iff {s : Set} : ¬ s.Nonempty ↔ s.IsEmpty := by
    constructor
    ·   exact fun h1 x h2 ↦ h1 ⟨x, h2⟩
    ·   exact fun h1 ⟨x, h2⟩ ↦ h1 x h2

theorem not_isEmpty_iff {s : Set}: ¬ s.IsEmpty ↔ s.Nonempty := by
    rw [←Classical.not_iff, Iff.comm, Classical.not_iff]
    exact not_nonempty_iff

theorem nonempty_iff_ne_empty {s : Set} : s.Nonempty ↔ s ≠ ∅ := by
    rw [Iff.comm, ←Classical.not_iff, Iff.comm, Classical.not_iff, not_nonempty_iff]
    exact isEmpty_iff_eq

theorem Nonempty.mem {x s : Set}: x ∈ s → s.Nonempty := fun h ↦ ⟨x, h⟩

axiom foundation (x : Set) : x.Nonempty → ∃ m : Set, (m ∈ x ∧ ∀ y ∈ x, y ∉ m)

theorem not_mem_self (s : Set) : s ∉ s := by
    have hs : (Sngl s).Nonempty := ⟨s, sngl_mem⟩
    have ⟨m, hm1, hm2⟩ := foundation (Sngl s) hs
    rw [sngl_mem_iff] at hm1; subst hm1
    exact hm2 m <| sngl_mem

noncomputable def Set.succ (s : Set) := ⋃ Dbl s (Sngl s)

theorem succ_mem_iff (x s : Set) : x ∈ s.succ ↔ x ∈ s ∨ x = s := by
    unfold Set.succ; rw [union_mem_iff]; simp [pair_mem_iff]
    constructor
    ·   intro ⟨y, hy1, hy2⟩; rcases hy2 with h | h <;> subst h
        ·   exact Or.inl hy1
        ·   rw [sngl_mem_iff] at hy1; exact Or.inr hy1
    ·   intro h; rcases h with h' | h'
        ·   exact ⟨s, h', Or.inl rfl⟩
        ·   subst h'; exact ⟨Sngl x, sngl_mem, Or.inr rfl⟩

def Set.Inductive (s : Set) := ∅ ∈ s ∧ (∀ x : Set, x ∈ s → x.succ ∈ s)

axiom infinity : ∃ s : Set, s.Inductive

noncomputable def CanonInf := Exists.choose infinity

theorem canonical_inf_inductive : CanonInf.Inductive :=
    Exists.choose_spec infinity

theorem empty_mem_base : ∅ ∈ CanonInf := canonical_inf_inductive.1

def is_succ_wff (s s' x: Nat) (_hdist : [s, s', x].Nodup := by decide) : Wff :=
    ((Wff.mem x s').iff
        ((Wff.mem x s).or (Wff.eq x s))
    ).all x

theorem Wff.is_succ_iff {σ : Assign ZF} (s s' x : Nat) (hdist : [s, s', x].Nodup) :
    Sat σ (is_succ_wff s s' x hdist) ↔ (σ s).succ = (σ s') := by
    simp [is_succ_wff]
    have hxs : x ≠ s := by grind
    have hxs' : x ≠ s' := by grind
    constructor
    ·   intro LHS; ext z
        change z ∈ (σ s).succ ↔ (z ∈ (σ s')); rw [succ_mem_iff]
        let τ := update σ x z; have h := LHS τ (update_agree_off)
        subst τ; simp [update_same] at h
        simp [update_other hxs, update_other hxs'] at h
        rwa [Iff.comm]
    ·   intro LHS τ hτ
        unfold AgreeOff at hτ
        unfold Set.succ at LHS; rw [← (hτ s hxs), ←(hτ s' hxs')]
        rw [←LHS]; show (τ x) ∈ (⋃Dbl (σ s) (Sngl (σ s))) ↔ (τ x) ∈  (σ s) ∨ τ x = σ s
        constructor
        ·   intro h; rw [union_mem_iff] at h
            obtain ⟨z, hz1, hz2⟩ := h
            rw [pair_mem_iff] at hz2
            rcases hz2 with h' | h' <;> subst h'
            ·   exact Or.inl hz1
            ·   rw [sngl_mem_iff] at hz1; exact Or.inr hz1
        ·   intro h; rw [union_mem_iff]; rcases h with h' | h'
            ·   refine ⟨σ s, h', pair_mem_left⟩
            ·   rw [h']; refine ⟨Sngl (σ s), sngl_mem, pair_mem_right⟩

example: Wff_Pred (fun s ↦ ∃ s', s.succ = s') := by
    intro s; refine ⟨is_succ_wff 0 1 2, one_param 0 s, ?_⟩
def set_isect_wff (x s y : Nat) (_hdist: [s, x, y].Nodup := by decide) : Wff :=
    ((Wff.mem y s).imp (Wff.mem x y)).all y

noncomputable def ZFIsect (family : Set) := by
    by_cases h : family.Nonempty
    ·   exact Separ (set_isect_wff 0 1 2) (one_param 1 family) (Exists.choose h)
    exact ∅

prefix:80 "⋂" => ZFIsect

theorem Wff.isect_mem_iff (s x : Set) (hs : s.Nonempty) : x ∈ ⋂s ↔ ∀ y, y ∈ s → x ∈ y := by
    unfold ZFIsect; simp [hs]; constructor
    ·   intro h y hy; have h' := separ_has_prop h
        unfold Wff.eval set_isect_wff at h'
        simp at h'; let σ := update (update (one_param 1 s) 0 x) 2 y
        have hσ : σ = update (update (one_param 1 s) 0 x) 2 y := by rfl
        have h'' := h' σ (update_agree_off)
        have h0 : σ 0 = x := by simp [hσ, update_other, update_same]
        have h1 : σ 1 = s := by simp [hσ, update_other, one_param_same]
        have h2 : σ 2 = y := by simp [hσ, update_same]
        rw [h0, h1, h2] at h''; exact h'' hy
    ·   intro hy; rw [separ_mem_iff]
        refine ⟨hy (Exists.choose hs) (Exists.choose_spec hs), ?_⟩
        simp [Wff.eval, set_isect_wff]; intro τ hτ1 hτ2
        have h0 := eq_of_agree_off hτ1 (j := 0) (by decide)
        rw [update_same] at h0
        have h2 := eq_of_agree_off hτ1 (j := 1) (by decide)
        rw [update_other (by decide), one_param_same] at h2
        rw [←h0]; rw [←h2] at hτ2
        exact hy (τ 2) hτ2

def is_inductive_wff (s e x y z : Nat) (hdist : [s, e, x, y, z].Nodup := by decide) : Wff :=
    (Wff.mem e s).and
    (( (Wff.mem x s).imp
        (((is_succ_wff x y z (by simp_all)).and (Wff.mem y s)).some y)
    ).all x)

theorem Wff.is_inductive_iff {τ : Assign ZF} (s e x y z : Nat) (hτ : τ e = ∅) (hdist : [s, e, x, y, z].Nodup := by decide) :
    Sat τ (is_inductive_wff s e x y z hdist) ↔ (τ s).Inductive := by
    unfold is_inductive_wff; have hxs : x ≠ s := by grind
    have hyx : y ≠ x := by grind
    have hys : y ≠ s := by grind
    simp; constructor
    ·   intro h
        obtain ⟨h1, h2⟩ := h; simp [hτ] at h1; refine ⟨h1, ?_⟩
        intro n hn; have h3 := h2 (update τ x n) update_agree_off
        have hts := update_other (σ := τ) (v := x) (a := n) hxs
        rw [← update_same (σ := τ) (v := x) (a := n), ←hts] at hn
        have h4 := h3 hn; have ⟨σ, hσ1, hσ2, hσ3⟩ := h4
        rw [Wff.is_succ_iff] at hσ2; simp [←hσ2] at hσ3
        have h5 : σ x = n := eq_of_agree_off' n hσ1 hyx (update_same); rw [h5] at hσ2 hσ3
        have h7 : σ s = τ s := eq_of_agree_off' (τ s) hσ1 hys (update_other hxs)
        exact h7 ▸ hσ3
    ·   intro ⟨hL1, hL2⟩; refine ⟨?_, ?_⟩
        ·   simpa [hτ]
        ·   intro ρ hρ; simp [Wff.is_succ_iff]
            intro h1; have hρ' := eq_of_agree_off hρ hxs
            rw [←hρ'] at h1; have hL3 := hL2 (ρ x) h1
            refine ⟨update ρ y (ρ x).succ, update_agree_off, ?_, ?_⟩
            ·   rw [update_same, update_other hyx]
            ·   simpa [update_same, update_other hys, ←hρ']

/- When I use this in Separ, 0 is the variable that will get used;
the only other free variable in omega_wff is 2, which will become ∅
when I use omega_assign
-/

def omega_wff : Wff := ((is_inductive_wff 1 2 3 4 5).imp (Wff.mem 0 1)).all 1

noncomputable def omega_assign := const_param ∅ --

noncomputable def ω : Set := Separ omega_wff omega_assign CanonInf

theorem mem_omega_iff {x : Set} : x ∈ ω ↔ ∀ y : Set, y.Inductive → x ∈ y := by
    constructor
    ·   intro hx y hy; unfold ω at hx; rw [separ_mem_iff] at hx
        obtain ⟨hx1, hx2⟩ := hx
        simp [Wff.eval, omega_assign, omega_wff] at hx2
        have h1 := hx2 (update (update (const_param ∅) 0 x) 1 y) update_agree_off
        have hρ : update (update (const_param ∅) 0 x) 1 y 2 = ∅ := by
            simp [update_other, const_param]
        have hy' : update (update (const_param ∅) 0 x) 1 y 1 = y := update_same
        rw [← hy', ←Wff.is_inductive_iff 1 2 3 4 5 hρ] at hy
        have h2 := h1 hy
        have hx' : update (update (const_param ∅) 0 x) 1 y 0 = x := by
            simp [update_other, update_same]
        rwa [hy', hx'] at h2
    ·   intro hy; unfold ω; simp [separ_mem_iff]
        refine ⟨hy CanonInf canonical_inf_inductive, ?_⟩
        simp [Wff.eval, omega_assign, omega_wff]; intro τ hτ h
        have hτ' : τ 2 = ∅ :=
            eq_of_agree_off' (j := 2) (∅ : Set) hτ (by decide) (update_other (by decide))
        simp [Wff.is_inductive_iff 1 2 3 4 5 hτ'] at h
        have hτ'' : τ 0 = x :=
            eq_of_agree_off' x hτ (Nat.zero_ne_one).symm update_same
        rw [hτ'']; exact hy (τ 1) h

theorem omega_assign_lemma {x : Nat} : update (const_param ∅) x ∅ = const_param ∅ := by
    funext y; by_cases hxy : x = y
    ·   subst hxy; exact update_same
    ·   exact update_other hxy

theorem omega_inductive : ω.Inductive := by
    refine ⟨?_, ?_⟩ <;> all_goals simp [mem_omega_iff]
    ·   exact fun _ hy ↦ hy.1
    ·   exact fun x h y hy ↦ hy.2 x <| h y hy

theorem omega_min (y : Set) : y.Inductive → ω ⊆ y := by
    intro hy x hx; rw [mem_omega_iff] at hx; exact hx y hy

theorem omega_unique (ω' : Set) : (∀ x : Set, (∀ y : Set, y.Inductive → x ∈ y) ↔ x ∈ ω') → ω = ω' := by
    intro h; apply eq_of_subset_of_subset
    ·   intro z hz; rw [mem_omega_iff] at hz; exact (h z).mp hz
    ·   intro z hz; rw [mem_omega_iff]; exact (h z).mpr hz

theorem induction_principle (y : Set) : y.Inductive → y ⊆ ω → y = ω := by
    intro hy hyω; apply eq_of_subset_of_subset y ω hyω <| omega_min y hy

theorem wff_induction (φ : Wff) (σ : Assign ZF) :
    Sat σ φ → (∀ n : Set, n ∈ (Separ φ σ ω) → n.succ ∈ (Separ φ σ ω)) → (Separ φ σ ω) = ω := by
    intro hbase ih; ext z;
    sorry
