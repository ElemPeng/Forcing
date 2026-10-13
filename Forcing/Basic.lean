axiom Set : Type
axiom zfmem : Set → Set → Prop

instance : Membership Set Set where mem x y := zfmem y x

axiom exist : Nonempty Set

@[ext] axiom zfexf (x y : Set) : (∀ s, s ∈ x ↔ s ∈ y) → x = y
axiom pair (x y : Set) : ∃ s : Set, ∀ z, (z ∈ s ↔ z = x ∨ z = y)

noncomputable def Dbl (x y : Set) := Exists.choose <| pair x y

noncomputable def Sngl (x : Set) := Dbl x x

theorem dbl_mem_iff {x y z : Set} : z ∈ Dbl x y ↔ z = x ∨ z = y :=
    ((Exists.choose_spec <| pair x y) z)

theorem dbl_mem_left {x y : Set} : x ∈ Dbl x y :=
    dbl_mem_iff.mpr <| Or.inl rfl

theorem dbl_mem_right {x y : Set} : y ∈ Dbl x y :=
    dbl_mem_iff.mpr <| Or.inr rfl

def Set.IsDbl (s : Set) := ∃ x y : Set, x ≠ y ∧ s = Dbl x y
def Set.IsSngl (s : Set) := ∃ x : Set, ∀ y : Set, (y ∈ s ↔ x = y)

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

noncomputable def CanonSet := Classical.choice exist

/- Need to be careful : pred should always be first order but the compiler
 doesn't enforce that; My Wff method does but I was getting ground down in
 doing first order logic-/

def SeparScheme (set : Set) (pred : Set → Prop) := ∃ sep : Set, ∀ x : Set, (x ∈ sep ↔ x ∈ set ∧ pred x)

def Set.IsEmpty (s : Set) := ∀ x : Set, x ∉ s
def Set.Nonempty (s : Set) := ∃ x : Set, x ∈ s

axiom empty_sep : SeparScheme CanonSet (fun x ↦ x ≠ x)

noncomputable def ZFempty := Exists.choose empty_sep

noncomputable instance : EmptyCollection Set where emptyCollection := ZFempty

theorem empty_is_empty : (∅ :Set).IsEmpty := by
    intro x hx; change x ∈ Exists.choose empty_sep at hx
    rw [(Exists.choose_spec empty_sep) x] at hx; simp_all

theorem empty_unique (s : Set) (hs : s.IsEmpty) : s = ∅ := by
    ext z; unfold Set.IsEmpty at hs; simp_all; exact empty_is_empty z

theorem not_mem_empty (s : Set) : s ∉ (∅ : Set) := (empty_is_empty) s

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
    unfold Set.succ; rw [union_mem_iff]; simp [dbl_mem_iff]
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

theorem canoninf_inductive : CanonInf.Inductive :=
    Exists.choose_spec infinity

theorem empty_mem_base : ∅ ∈ CanonInf := canoninf_inductive.1

axiom isect_sep (family : Set) : SeparScheme (⋃family) (fun x ↦ ∀ a ∈ family, x ∈ a)

noncomputable def ZFIsect (family : Set) := Exists.choose <| isect_sep family

prefix:80 "⋂" => ZFIsect

theorem Wff.isect_mem_iff (s x : Set) (hs : s.Nonempty) : x ∈ ⋂s ↔ ∀ y, y ∈ s → x ∈ y := by
    unfold ZFIsect; have h := Exists.choose_spec <| isect_sep s; constructor
    ·   intro LHS; rw [h x] at LHS; exact LHS.2
    ·   intro LHS; rw [h x]; refine ⟨?_, LHS⟩
        rw [union_mem_iff]; have ⟨a, ha⟩:= hs; exact ⟨a, LHS a ha, ha⟩
/-
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

theorem induction_principle {y : Set} : y.Inductive → y ⊆ ω → y = ω := by
    intro hy hyω; apply eq_of_subset_of_subset y ω hyω <| omega_min y hy

theorem wff_induction (φ : Wff) (σ : Assign ZF) :
    ∅ ∈ (Separ φ σ ω) → (∀ n : Set, n ∈ (Separ φ σ ω) → n.succ ∈ (Separ φ σ ω)) → (Separ φ σ ω) = ω := by
    intro hbase ih; have hind : (Separ φ σ ω).Inductive := ⟨hbase, ih⟩
    apply induction_principle hind (separ_is_subset)

def Set.Transitive (s : Set) := ∀ a : Set, a ∈ s → a ⊆ s

def is_transitive_wff (s a b : Nat) : Wff :=
    ((Wff.mem a s).imp ((Wff.mem b a).imp (Wff.mem b s))).all s

noncomputable def Set.Pair (x y : Set) := Dbl (Sngl x) (Dbl x y)

noncomputable def Prod.ZF (p : Set × Set) := Set.Pair p.1 p.2

def Set.IsPair (s : Set) := ∃ x y : Set, s = Set.Pair x y

def Set.IsRelation (r : Set) := ∀ x : Set, x ∈ r → x.IsPair

theorem fst_of_pair (p : Set) (hp : p.IsPair) : ∃ x : Set, ∀ a : Set, a ∈ p → x ∈ a := by
    unfold Set.IsPair Set.Pair at hp; obtain ⟨x, y, hxy⟩ := hp
    refine ⟨x, ?_⟩; intro a ha; rw [hxy] at ha; rw [dbl_mem_iff] at ha
    rcases ha with h | h
    ·   subst h; exact sngl_mem
    ·   subst h; exact dbl_mem_left

theorem snd_of_pair (p : Set)
-/
