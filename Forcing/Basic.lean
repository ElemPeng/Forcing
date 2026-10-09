axiom Set : Type
axiom zfmem : Set → Set → Prop

instance : Membership Set Set where mem x y := zfmem x y

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

axiom union (s : Set) : ∃ u : Set, ∀ x, (x ∈ u ↔ ∃ a : Set, x ∈ a ∧ a ∈ s)

noncomputable def U (s : Set) := Exists.choose <| union s

theorem union_mem_iff {s a : Set} : a ∈ U s ↔ ∃ x, a ∈ x ∧ x ∈ s :=
    (Exists.choose_spec <| union s) a

theorem union_mem_of_mem_of_mem {s a x : Set} : a ∈ x → x ∈ s → a ∈ U s :=
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

abbrev Assign (ℳ : Model) := Nat → ℳ.M

def AgreeOff {ℳ : Model} (i : Nat) (σ τ : Assign ℳ) := ∀ j : Nat, i ≠ j → σ j = τ j

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
    rw [←Classical.not_iff, Iff.comm, Classical.not_iff]
    rw [Classical.not_and_iff_not_or_not, ←Wff.not_iff]
    rw [←Wff.not_iff, ← Wff.or_iff, Wff.or]
    unfold Sat; conv => (lhs; congr; unfold Sat Sat; rw [Classical.not_not])

def update {ℳ : Model} : Assign ℳ → Nat → ℳ.M → Assign ℳ :=
    fun σ v a j ↦ if v = j then a else σ j

theorem update_same {ℳ : Model} {σ : Assign ℳ} {v : Nat} {a : ℳ.M} :
    update σ v a v = a := by unfold update; rw [ite_eq_left rfl]

theorem update_other {ℳ : Model} {σ : Assign ℳ} {v n : Nat} {a : ℳ.M} :
    v ≠ n → update σ v a n = σ n := by
    intro hne; unfold update; rw [ite_eq_right hne]

theorem update_agree_off {ℳ : Model} {σ : Assign ℳ} {v : Nat} {a : ℳ.M} :
    AgreeOff v σ (update σ v a) := fun _ hn ↦ (update_other hn).symm

def ZF : Model := ⟨Set, zfmem⟩

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
    simp at ha'; exact ha' rfl

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

noncomputable def Set.succ (s : Set) := U <| Dbl s (Sngl s)

def Set.Inductive (s : Set) := ∅ ∈ s ∧ (∀ x : Set, x ∈ s → x.succ ∈ s)

axiom infinity : ∃ s : Set, s.Inductive

def is_succ_wff (s s' x: Nat) (_hdist : [s, s', x].Nodup := by decide)
: Wff :=
    ((Wff.mem x s').iff
        ((Wff.mem x s).or (Wff.eq x s))
    ).all x

def is_inductive_wff (s e x y z : Nat) (_hdist : [s, e, x, y, z].Nodup := by decide) : Wff :=
    (Wff.mem e x).and
    ((
        (is_succ_wff s y z (by simp_all)).some y
    ).all x)

def omega_wff : Wff := ((is_inductive_wff 1 2 3 4 5).imp (Wff.mem 0 1)).all 1

noncomputable def omega_assign := const_param (∅)
