axiom Set : Type
axiom zfmem : Set → Set → Prop

instance : Membership Set Set where mem x y := zfmem x y

axiom exist : Nonempty Set
axiom zfexf (x y : Set) : (∀ s, s ∈ x ↔ s ∈ y) → x = y
axiom pair (x y : Set) : ∃ s : Set, ∀ z, (z ∈ s ↔ z = x ∨ z = y)

noncomputable def Dbl (x y : Set) := Exists.choose <| pair x y

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

inductive Formula where
    | mem : Nat → Nat → Formula
    | eq : Nat → Nat → Formula
    | not : Formula → Formula
    | imp : Formula → Formula → Formula
    | all : Nat → Formula → Formula

structure Model where
    M : Type
    E : M → M → Prop

abbrev Assign (ℳ : Model) := Nat → ℳ.M

def AgreeOff {ℳ : Model} (i : Nat) (σ τ : Assign ℳ) := ∀ j : Nat, i ≠ j → σ j = τ j

def Sat {ℳ : Model} (σ : Assign ℳ) : Formula → Prop
    | Formula.mem i j => ℳ.E (σ i) (σ j)
    | Formula.eq i j => (σ i) = (σ j)
    | Formula.not φ => ¬(Sat σ φ)
    | Formula.imp φ ψ => (Sat σ φ) → (Sat σ ψ)
    | Formula.all i φ => ∀ τ : Assign ℳ, AgreeOff i σ τ → (Sat τ φ)

def Formula.or (φ ψ : Formula) := φ.not.imp ψ

def Formula.and (φ ψ : Formula) := (φ.imp ψ.not).not

def Formula.iff (φ ψ : Formula) := (φ.imp ψ).and (ψ.imp φ)

def Formula.some (i : Nat) (φ : Formula) := ((φ.not).all i).not

theorem Formula.not_iff {ℳ : Model} {σ : Assign ℳ} {φ : Formula} :
    Sat σ φ.not ↔ ¬(Sat σ φ) := by rfl

theorem Formula.imp_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ: Formula} :
    Sat σ (φ.imp ψ) ↔ (Sat σ φ) → (Sat σ ψ) := by rfl

theorem Formula.all_iff {ℳ : Model} {σ : Assign ℳ} {i : Nat} {φ : Formula} :
    Sat σ (φ.all i) ↔ ∀ τ : Assign ℳ, AgreeOff i σ τ → (Sat τ φ) := by rfl

theorem Formula.or_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ : Formula} :
    Sat σ (φ.or ψ) ↔ (Sat σ φ) ∨ (Sat σ ψ) := by
    unfold Formula.or; rw [Classical.or_iff_not_imp_left]; rfl

theorem Formula.and_iff {ℳ : Model} {σ : Assign ℳ} {φ ψ : Formula} :
    Sat σ (φ.and ψ) ↔ (Sat σ φ) ∧ (Sat σ ψ) := by
    unfold Formula.and; change ¬ (Sat σ (φ.imp ψ.not)) ↔ Sat σ φ ∧ Sat σ ψ
    rw [←Classical.not_iff, Iff.comm, Classical.not_iff]
    rw [Classical.not_and_iff_not_or_not, ←Formula.not_iff]
    rw [←Formula.not_iff, ← Formula.or_iff, Formula.or]
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


/-
axiom separ_scheme (φ : Set → Prop) (x : Set) :
∃ y : Set, ∀ a : Set, (a ∈ y ↔ a ∈ x ∧ φ a)

noncomputable def Separ (φ : Set → Prop) (x : Set) := Exists.choose (separ_scheme φ x)

theorem separ_is_subset {φ : Set → Prop} {x : Set} : Separ φ x ⊆ x :=
    fun a ha ↦ ((Exists.choose_spec (separ_scheme φ x) a).mp ha).1

theorem separ_has_prop {φ : Set → Prop} {x a : Set} : a ∈ Separ φ x → φ a :=
    fun ha ↦ ((Exists.choose_spec (separ_scheme φ x) a).mp ha).2

theorem separ_mem_iff {φ : Set → Prop} {x a : Set} : a ∈ Separ φ x ↔ (a ∈ x ∧ φ a) :=
    Exists.choose_spec (separ_scheme φ x) a

theorem exists_empty : ∃ s : Set, ∀ a : Set, a ∉ s := by
    have ⟨x⟩ := exist; refine ⟨Separ (fun _ ↦ False) x, fun a ↦ separ_has_prop⟩
-/
