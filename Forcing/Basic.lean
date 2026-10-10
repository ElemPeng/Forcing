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

theorem eq_of_agree_off {ℳ : Model} {i j : Nat} {σ τ : Assign ℳ} :
    AgreeOff i σ τ → i ≠ j → σ j = τ j := fun h1 h2 ↦ h1 j h2

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

theorem Wff.mem_iff {ℳ : Model} {σ : Assign ℳ} {i j : Nat} :
    Sat σ (mem i j) ↔ ℳ.E (σ i) (σ j) := by rfl

theorem Wff.eq_iff {ℳ : Model} {σ : Assign ℳ} {i j : Nat} :
    Sat σ (eq i j) ↔ (σ i) = (σ j) := by rfl

theorem Wff.not_iff {ℳ : Model} {σ : Assign ℳ} {φ : Wff} :
    Sat σ φ.not ↔ ¬(Sat σ φ) := by rfl

theorem Wff.imp_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ: Wff} :
    Sat σ (φ.imp ψ) ↔ (Sat σ φ) → (Sat σ ψ) := by rfl

theorem Wff.all_iff {ℳ : Model} {σ : Assign ℳ} {i : Nat} {φ : Wff} :
    Sat σ (φ.all i) ↔ ∀ τ : Assign ℳ, AgreeOff i σ τ → (Sat τ φ) := by rfl

theorem Wff.or_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ : Wff} :
    Sat σ (φ.or ψ) ↔ (Sat σ φ) ∨ (Sat σ ψ) := by
    unfold Wff.or; rw [Classical.or_iff_not_imp_left]; rfl

theorem Wff.and_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ : Wff} :
    Sat σ (φ.and ψ) ↔ (Sat σ φ) ∧ (Sat σ ψ) := by
    unfold Wff.and; change ¬ (Sat σ (φ.imp ψ.not)) ↔ Sat σ φ ∧ Sat σ ψ
    rw [not_iff_comm, not_and, Wff.imp_iff, not_iff]

theorem Wff.iff_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ : Wff} :
    Sat σ (φ.iff ψ) ↔ ((Sat σ φ) ↔ (Sat σ ψ)) := by
    unfold iff; rw [and_iff, imp_iff, imp_iff,
        iff_iff_implies_and_implies (a := Sat σ φ)]

theorem Wff.some_iff {ℳ : Model} {σ : Assign ℳ} {i : Nat} {φ : Wff} :
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

abbrev ZF : Model := ⟨Set, zfmem⟩

def Wff.eval {ℳ : Model} (σ : Assign ℳ) (φ : Wff) (v : Nat) (a : ℳ.M) :=
    Sat (update σ v a) φ

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

theorem exists_empty : ∃ s : Set, ∀ a : Set, a ∉ s := by
    have ⟨x⟩ := exist; refine ⟨Separ (Wff.eq 0 0).not (const_param x) x, ?_⟩
    intro a ha; rw [separ_mem_iff] at ha; have ⟨_, ha'⟩ := ha;
    unfold Wff.eval update Sat Sat at ha'
    simp at ha'

noncomputable def ZFempty : Set := Exists.choose exists_empty

noncomputable instance : EmptyCollection Set where emptyCollection := ZFempty

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

def is_succ_wff (s s' x: Nat) (_hdist : [s, s', x].Nodup := by decide)
: Wff :=
    ((Wff.mem x s').iff
        ((Wff.mem x s).or (Wff.eq x s))
    ).all x

theorem Wff.is_succ_iff {σ : Assign ZF} (s s' x : Nat) (hdist : [s, s', x].Nodup):
    Sat σ (is_succ_wff s s' x hdist) ↔ (σ s).succ = (σ s') := by
    simp [is_succ_wff, all_iff, iff_iff, or_iff]
    have hxs : x ≠ s := by grind
    have hxs' : x ≠ s' := by grind
    constructor
    ·   intro LHS; ext z
        change z ∈ (σ s).succ ↔ (z ∈ (σ s')); rw [succ_mem_iff]
        let τ := update σ x z; have h := LHS τ (update_agree_off)
        simp [mem_iff, eq_iff] at h; subst τ; simp [update_same] at h
        simp [update_other hxs, update_other hxs'] at h
        rwa [Iff.comm]
    ·   intro LHS τ hτ; simp [mem_iff, eq_iff]
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


def is_inductive_wff (s e x y z : Nat) (_hdist : [s, e, x, y, z].Nodup := by decide) : Wff :=
    (Wff.mem e s).and
    (( (Wff.mem x s).imp
        (((is_succ_wff x y z (by simp_all)).and (Wff.mem y s)).some y)
    ).all x)

/- When I use this in Separ, 0 is the variable that will get used;
the only other free variable in omega_wff is 2, which will become ∅
when I use omega_assign
-/

def omega_wff : Wff := ((is_inductive_wff 1 2 3 4 5).imp (Wff.mem 0 1)).all 1

noncomputable def omega_assign := const_param (∅)

noncomputable def ω : Set := Separ omega_wff omega_assign CanonInf

theorem omega_inductive : ω.Inductive := by
    unfold ω; constructor
    ·   rw [separ_mem_iff]; refine ⟨empty_mem_base, ?_⟩
        unfold Wff.eval; unfold omega_wff omega_assign
        unfold Sat AgreeOff; intro τ hj; rw [Wff.imp_iff]
        intro hS; have h0 := hj 0 (by decide)
        unfold update at h0; simp at h0
        have h2 := hj 2 (by decide)
        simp [update, const_param] at h2
        unfold is_inductive_wff at hS
        unfold Sat; rw [Wff.and_iff] at hS
        have ⟨hS1, hS2⟩ := hS; simp [Sat] at hS1
        exact h0 ▸ h2 ▸ hS1
    ·   intro x hx; rw [separ_mem_iff] at hx ⊢
        have ⟨hx1, hx2⟩ := hx; refine ⟨?_, ?_⟩
        ·   exact canonical_inf_inductive.2 x hx1
        ·   simp [Wff.eval, omega_assign, omega_wff] at hx2 ⊢
            rw [Wff.all_iff] at hx2 ⊢; intro τ hτ
            unfold AgreeOff update const_param at hx2 hτ
            let σ : Assign ZF :=  fun j ↦  (if 0 = j then x else (∅ : Set))
            have hσ : ∀ j : Nat, (if 0 = j then x else (∅ : Set)) = σ j := by
                intro j; rfl
            have hx2' := hx2 σ
            have hσ' : (∀ (j : Nat), 1 ≠ j → (if 0 = j then x else ∅) = σ j) := by
                intro j hj; exact hσ j
            have hx2'' := hx2' hσ'
            rw [Wff.imp_iff] at hx2'' ⊢; intro h1
            unfold is_inductive_wff at h1 hx2''
            rw [Wff.and_iff] at hx2'' h1
