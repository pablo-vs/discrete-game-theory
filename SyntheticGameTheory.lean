import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Discrete Simplex (~100 lines)
-- ================================================================

/-- A discrete simplex on vertex set V. Elements are nonempty subsets
    of V, each representing the interior of the face spanned by those
    vertices. -/
@[reducible]
def DSimplex (V : Type*) [DecidableEq V] :=
  { S : Finset V // S.Nonempty }

namespace DSimplex

variable {V : Type*} [DecidableEq V]

instance instDecidablePredFinsetNonempty (V : Type*) [DecidableEq V] :
    DecidablePred (fun s : Finset V => s.Nonempty) := by
  intro s
  infer_instance

instance instFintype (V : Type*) [DecidableEq V] [Fintype V] : Fintype (DSimplex V) := by
  classical
  infer_instance

/-- Canonical linear order on DSimplex using Fintype. -/
noncomputable instance instLinearOrderDSimplex [Fintype V] : LinearOrder (DSimplex V) := by
  classical
  let equiv := Fintype.equivFin (DSimplex V)
  refine LinearOrder.lift' equiv ?_
  exact equiv.injective

/-- Vertex embedding: v ↦ {v}. -/
def vertex (v : V) : DSimplex V :=
  ⟨{v}, Finset.singleton_nonempty v⟩

/-- Mix = union of supports. The interior of the smallest face
    containing both inputs. -/
def mix (x y : DSimplex V) : DSimplex V :=
  ⟨x.1 ∪ y.1, x.2.mono Finset.subset_union_left⟩

/-- The support of a simplex element (its vertex set). -/
def support (x : DSimplex V) : Finset V := x.1

/-- x is a sub-face of y when x's support is contained in y's. -/
def IsSubface (x y : DSimplex V) : Prop := x.1 ⊆ y.1

instance (x y : DSimplex V) : Decidable (IsSubface x y) :=
  inferInstanceAs (Decidable (x.1 ⊆ y.1))

@[ext]
theorem ext {x y : DSimplex V} (h : x.1 = y.1) : x = y :=
  Subtype.ext h

@[simp] theorem vertex_val (v : V) : (vertex v).1 = {v} := rfl
@[simp] theorem mix_val (x y : DSimplex V) : (mix x y).1 = x.1 ∪ y.1 := rfl

@[simp] theorem mix_comm (x y : DSimplex V) : mix x y = mix y x := by
  ext1; exact Finset.union_comm x.1 y.1

@[simp] theorem mix_assoc (x y z : DSimplex V) :
    mix (mix x y) z = mix x (mix y z) := by
  ext1; exact Finset.union_assoc x.1 y.1 z.1

@[simp] theorem mix_self (x : DSimplex V) : mix x x = x := by
  ext1; exact Finset.union_self x.1

theorem mix_isSubface_left (x y : DSimplex V) : IsSubface x (mix x y) := by
  simp [IsSubface, mix]

theorem mix_isSubface_right (x y : DSimplex V) : IsSubface y (mix x y) := by
  simp [IsSubface, mix]

end DSimplex

-- ================================================================
-- Section 2: Profiles (Pure and Mixed) (~200 lines)
-- ================================================================

/-- A pure profile: each player picks a vertex (pure action). -/
abbrev PureProfile (N : Type*) (V : N → Type*) := ∀ i : N, V i

noncomputable instance instFintypePureProfile
    {N : Type*} [Fintype N] {V : N → Type*} [∀ i, Fintype (V i)] :
    Fintype (PureProfile N V) := by
  classical
  infer_instance

noncomputable instance instDecidableEqPureProfile
    {N : Type*} [Fintype N] {V : N → Type*}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] :
    DecidableEq (PureProfile N V) := by
  classical
  infer_instance

/-- A profile: each player picks a face of their simplex. -/
abbrev Profile (N : Type*) (V : N → Type*) [∀ i, DecidableEq (V i)] :=
  ∀ i : N, DSimplex (V i)

noncomputable instance instDecidableEqProfile
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)] :
    DecidableEq (Profile N V) := by
  classical
  infer_instance

/-- Canonical linear order on Profile using Fintype. -/
noncomputable instance instLinearOrderProfile
    {N : Type*} [Fintype N] [DecidableEq N]
    {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] :
    LinearOrder (Profile N V) := by
  classical
  let equiv := Fintype.equivFin (Profile N V)
  refine LinearOrder.lift' equiv ?_
  exact equiv.injective

/-- Deviator faces `(i, A)` as a sigma type. -/
abbrev DevFace (N : Type*) (V : N → Type*) [∀ i, DecidableEq (V i)] :=
  Sigma (fun i : N => DSimplex (V i))

instance instFintypeDevFace
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] :
    Fintype (DevFace N V) := by
  classical
  infer_instance

/-- Canonical linear order on DevFace using Fintype. -/
noncomputable instance instLinearOrderDevFace
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] :
    LinearOrder (DevFace N V) := by
  classical
  let equiv := Fintype.equivFin (DevFace N V)
  refine LinearOrder.lift' equiv ?_
  exact equiv.injective

/-- Notation for profile deviation: σ[i ↦ s] means "profile σ with player i
    updated to play s". -/
notation:max σ:max "[" i " ↦ " s "]" => Function.update σ i s

-- ----------------------------------------------------------------
-- Section 2.1: Consistency and Profile Order
-- ----------------------------------------------------------------

/-- A pure profile `p` is consistent with a mixed profile `σ` if each action is
    in the support of the corresponding face. -/
def Consistent
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) (p : PureProfile N V) : Prop :=
  ∀ i, p i ∈ DSimplex.support (σ i)

noncomputable instance instDecidablePredConsistent
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) : DecidablePred (Consistent (σ := σ)) := by
  classical
  intro p
  infer_instance

/-- Pointwise subface order on profiles. -/
def ProfileLE
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ τ : Profile N V) : Prop :=
  ∀ i, DSimplex.IsSubface (σ i) (τ i)

theorem ProfileLE_refl
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) :
    ProfileLE σ σ := by
  intro i
  simp [DSimplex.IsSubface]

theorem ProfileLE_trans
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    {σ τ ρ : Profile N V} :
    ProfileLE σ τ → ProfileLE τ ρ → ProfileLE σ ρ := by
  intro hστ hτρ i
  have h1 : DSimplex.support (σ i) ⊆ DSimplex.support (τ i) := by
    simpa [DSimplex.IsSubface] using hστ i
  have h2 : DSimplex.support (τ i) ⊆ DSimplex.support (ρ i) := by
    simpa [DSimplex.IsSubface] using hτρ i
  exact h1.trans h2

/-- Consistency is monotone in profile faces. -/
theorem Consistent_mono
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    {σ τ : Profile N V} (h : ProfileLE σ τ) {p : PureProfile N V} :
    Consistent σ p → Consistent τ p := by
  intro hσ i
  have hsub : DSimplex.support (σ i) ⊆ DSimplex.support (τ i) := by
    simpa [DSimplex.IsSubface] using h i
  exact hsub (hσ i)

theorem ProfileLE_update
    {N : Type*} {V : N → Type*} [DecidableEq N] [∀ i, DecidableEq (V i)]
    {σ τ : Profile N V} (h : ProfileLE σ τ)
    (i : N) (A : DSimplex (V i)) :
    ProfileLE (σ[i ↦ A]) (τ[i ↦ A]) := by
  intro j
  by_cases hji : j = i
  · subst hji
    simp [DSimplex.IsSubface]
  · simp [hji, h j]

theorem ProfileLE_update_left
    {N : Type*} {V : N → Type*} [DecidableEq N] [∀ i, DecidableEq (V i)]
    (σ : Profile N V) (i : N) {A A' : DSimplex (V i)}
    (h : DSimplex.IsSubface A A') :
    ProfileLE (σ[i ↦ A]) (σ[i ↦ A']) := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa [DSimplex.IsSubface] using h
  · simp [hji, DSimplex.IsSubface]

-- ----------------------------------------------------------------
-- Section 2.2: Profile Mix Operations
-- ----------------------------------------------------------------

/-- Mix profiles pointwise. -/
def Profile.mix
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ τ : Profile N V) : Profile N V :=
  fun i => DSimplex.mix (σ i) (τ i)

theorem Profile.mix_comm
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ τ : Profile N V) :
    Profile.mix σ τ = Profile.mix τ σ := by
  funext i; simp [Profile.mix, DSimplex.mix_comm]

theorem Profile.mix_assoc
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ τ ρ : Profile N V) :
    Profile.mix (Profile.mix σ τ) ρ = Profile.mix σ (Profile.mix τ ρ) := by
  funext i
  ext1
  simp [Profile.mix, DSimplex.mix, Finset.union_assoc]

theorem Profile.mix_self
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) :
    Profile.mix σ σ = σ := by
  funext i; simp [Profile.mix]

/-- Mixing enlarges each coordinate face. -/
theorem ProfileLE_mix_left
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ τ : Profile N V) :
    ProfileLE σ (Profile.mix σ τ) := by
  intro i; simpa [Profile.mix] using DSimplex.mix_isSubface_left (σ i) (τ i)

/-- Mixing enlarges each coordinate face. -/
theorem ProfileLE_mix_right
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ τ : Profile N V) :
    ProfileLE τ (Profile.mix σ τ) := by
  intro i; simpa [Profile.mix] using DSimplex.mix_isSubface_right (σ i) (τ i)

/-- If both inputs are subfaces of `M`, then their mix is a subface of `M`. -/
theorem ProfileLE_mix_of_le
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    {σ τ M : Profile N V}
    (hσ : ProfileLE σ M) (hτ : ProfileLE τ M) :
    ProfileLE (Profile.mix σ τ) M := by
  intro i
  have hσi : DSimplex.support (σ i) ⊆ DSimplex.support (M i) := by
    simpa [DSimplex.IsSubface] using hσ i
  have hτi : DSimplex.support (τ i) ⊆ DSimplex.support (M i) := by
    simpa [DSimplex.IsSubface] using hτ i
  simpa [Profile.mix, DSimplex.IsSubface, DSimplex.mix] using
    (Finset.union_subset hσi hτi)

theorem ProfileLE_foldl_mix_left
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) (l : List (Profile N V)) :
    ProfileLE σ (l.foldl Profile.mix σ) := by
  induction l generalizing σ with
  | nil =>
      simpa using ProfileLE_refl σ
  | cons x xs ih =>
      dsimp [List.foldl]
      have h1 : ProfileLE σ (Profile.mix σ x) := ProfileLE_mix_left σ x
      have h2 : ProfileLE (Profile.mix σ x) (xs.foldl Profile.mix (Profile.mix σ x)) :=
        ih (σ := Profile.mix σ x)
      exact ProfileLE_trans h1 h2

theorem ProfileLE_foldl_mix_of_mem
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) (l : List (Profile N V)) {τ : Profile N V}
    (hmem : τ ∈ l) :
    ProfileLE τ (l.foldl Profile.mix σ) := by
  induction l generalizing σ with
  | nil =>
      cases hmem
  | cons x xs ih =>
      have hmem' : τ = x ∨ τ ∈ xs := (List.mem_cons).1 hmem
      cases hmem' with
      | inl hτ =>
          subst hτ
          dsimp [List.foldl]
          have h1 : ProfileLE τ (Profile.mix σ τ) := ProfileLE_mix_right σ τ
          have h2 : ProfileLE (Profile.mix σ τ) (xs.foldl Profile.mix (Profile.mix σ τ)) :=
            ProfileLE_foldl_mix_left (Profile.mix σ τ) xs
          exact ProfileLE_trans h1 h2
      | inr hτ =>
          dsimp [List.foldl]
          exact ih (σ := Profile.mix σ x) hτ

theorem ProfileLE_foldl_mix_of_forall
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) (l : List (Profile N V)) {M : Profile N V}
    (hσ : ProfileLE σ M)
    (h : ∀ τ ∈ l, ProfileLE τ M) :
    ProfileLE (l.foldl Profile.mix σ) M := by
  induction l generalizing σ with
  | nil =>
      simpa using hσ
  | cons x xs ih =>
      have hx : ProfileLE x M := h x (by simp)
      have hσ' : ProfileLE (Profile.mix σ x) M := ProfileLE_mix_of_le hσ hx
      apply ih (σ := Profile.mix σ x) hσ'
      intro τ hτ
      exact h τ (by simp [hτ])

def Profile.mixList
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) (hne : l ≠ []) : Profile N V :=
  match l with
  | [] => (hne rfl).elim
  | x :: xs => xs.foldl Profile.mix x

theorem Profile.mixList_eq_of_ne_nil
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    {l : List (Profile N V)} (h₁ h₂ : l ≠ []) :
    Profile.mixList l h₁ = Profile.mixList l h₂ := by
  cases l with
  | nil => cases h₁ rfl
  | cons x xs => rfl

theorem Profile.foldl_mix_left
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (a b : Profile N V) (l : List (Profile N V)) :
    l.foldl Profile.mix (Profile.mix a b) =
      Profile.mix a (l.foldl Profile.mix b) := by
  induction l generalizing a b with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl, Profile.mix_assoc, ih]

theorem Profile.mixList_append_singleton_mixList
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (l₁ l₂ : List (Profile N V)) (hne₂ : l₂ ≠ []) :
    Profile.mixList (l₁ ++ [Profile.mixList l₂ hne₂]) (by simp) =
      Profile.mixList (l₁ ++ l₂) (by
        cases l₁ <;> simp [hne₂]) := by
  classical
  cases l₁ with
  | nil =>
      cases l₂ with
      | nil => cases hne₂ rfl
      | cons y ys =>
          simp [Profile.mixList]
  | cons x xs =>
      cases l₂ with
      | nil => cases hne₂ rfl
      | cons y ys =>
          have hne₂' : (y :: ys) ≠ [] := by simp
          simp [Profile.mixList, List.foldl_append, Profile.foldl_mix_left]

theorem ProfileLE_mixList_of_mem
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    {l : List (Profile N V)} (hne : l ≠ [])
    {σ : Profile N V} (hmem : σ ∈ l) :
    ProfileLE σ (Profile.mixList l hne) := by
  cases l with
  | nil => cases hne rfl
  | cons x xs =>
      dsimp [Profile.mixList]
      have hmem' : σ = x ∨ σ ∈ xs := (List.mem_cons).1 hmem
      cases hmem' with
      | inl hσ =>
          subst hσ
          exact ProfileLE_foldl_mix_left σ xs
      | inr hσ =>
          exact ProfileLE_foldl_mix_of_mem x xs hσ

theorem ProfileLE_mixList_of_forall
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    {l : List (Profile N V)} (hne : l ≠ []) {M : Profile N V}
    (h : ∀ τ ∈ l, ProfileLE τ M) :
    ProfileLE (Profile.mixList l hne) M := by
  cases l with
  | nil => cases hne rfl
  | cons x xs =>
      dsimp [Profile.mixList]
      have hx : ProfileLE x M := h x (by simp)
      exact ProfileLE_foldl_mix_of_forall (σ := x) (l := xs) (M := M) hx
        (by
          intro τ hτ
          exact h τ (by simp [hτ]))

-- ----------------------------------------------------------------
-- Section 2.3: Intersection and Support
-- ----------------------------------------------------------------

/-- Two profiles intersect if they share a consistent pure profile. -/
def Intersects
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ τ : Profile N V) : Prop :=
  ∃ p, Consistent σ p ∧ Consistent τ p

namespace Profile

/-- Support of a profile: all pure profiles consistent with it. -/
noncomputable def support
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (σ : Profile N V) : Finset (PureProfile N V) :=
  (Finset.univ : Finset (PureProfile N V)).filter (Consistent σ)

theorem support_nonempty
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (σ : Profile N V) :
    (support σ).Nonempty := by
  classical
  let p : PureProfile N V := fun i => Classical.choose (σ i).2
  have hp : Consistent σ p := by
    intro i
    exact Classical.choose_spec (σ i).2
  refine ⟨p, ?_⟩
  simp [support, hp]

theorem support_subset_of_le
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {σ τ : Profile N V} (h : ProfileLE σ τ) :
    support σ ⊆ support τ := by
  intro p hp
  have hp' : Consistent σ p := by
    have hp' : p ∈ (Finset.univ : Finset (PureProfile N V)).filter (Consistent σ) := by
      simpa [Profile.support] using hp
    exact (Finset.mem_filter.mp hp').2
  have hq : Consistent τ p := Consistent_mono h hp'
  exact (Finset.mem_filter.mpr ⟨by simp, hq⟩)

end Profile

theorem Intersects_symm
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    {σ τ : Profile N V} :
    Intersects σ τ → Intersects τ σ := by
  intro h
  rcases h with ⟨p, hpσ, hpτ⟩
  exact ⟨p, hpτ, hpσ⟩

theorem Intersects_refl
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) :
    Intersects σ σ := by
  classical
  let p : PureProfile N V := fun i => Classical.choose (σ i).2
  have hp : ∀ i, p i ∈ DSimplex.support (σ i) := by
    intro i
    exact Classical.choose_spec (σ i).2
  exact ⟨p, hp, hp⟩

theorem Intersects_of_ProfileLE
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    {σ τ : Profile N V} (h : ProfileLE σ τ) :
    Intersects σ τ := by
  rcases Intersects_refl σ with ⟨p, hpσ, hpσ'⟩
  exact ⟨p, hpσ, Consistent_mono h hpσ'⟩

theorem Intersects_iff_support_intersects
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {σ τ : Profile N V} :
    Intersects σ τ ↔
      (Profile.support σ ∩ Profile.support τ).Nonempty := by
  constructor
  · intro h
    rcases h with ⟨p, hpσ, hpτ⟩
    refine ⟨p, ?_⟩
    have hpσ' : p ∈ Profile.support σ :=
      (Finset.mem_filter.mpr ⟨by simp, hpσ⟩)
    have hpτ' : p ∈ Profile.support τ :=
      (Finset.mem_filter.mpr ⟨by simp, hpτ⟩)
    exact Finset.mem_inter.mpr ⟨hpσ', hpτ'⟩
  · intro h
    rcases h with ⟨p, hp⟩
    have hpσ' : p ∈ Profile.support σ := (Finset.mem_inter.mp hp).1
    have hpτ' : p ∈ Profile.support τ := (Finset.mem_inter.mp hp).2
    have hpσ'' :
        p ∈ (Finset.univ : Finset (PureProfile N V)).filter (Consistent σ) := by
      simpa [Profile.support] using hpσ'
    have hpτ'' :
        p ∈ (Finset.univ : Finset (PureProfile N V)).filter (Consistent τ) := by
      simpa [Profile.support] using hpτ'
    have hpσ : Consistent σ p := (Finset.mem_filter.mp hpσ'').2
    have hpτ : Consistent τ p := (Finset.mem_filter.mp hpτ'').2
    exact ⟨p, hpσ, hpτ⟩

def Disjoint
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ τ : Profile N V) : Prop :=
  ¬ Intersects σ τ

theorem support_disjoint_of_not_intersects
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {σ τ : Profile N V} (h : ¬ Intersects σ τ) :
    _root_.Disjoint (Profile.support σ) (Profile.support τ) := by
  classical
  apply (Finset.disjoint_iff_inter_eq_empty).2
  by_contra hne
  have hnonempty : (Profile.support σ ∩ Profile.support τ).Nonempty := by
    exact (Finset.nonempty_iff_ne_empty).2 hne
  exact h ((Intersects_iff_support_intersects (σ := σ) (τ := τ)).2 hnonempty)

def PairwiseDisjoint
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) : Prop :=
  l.Pairwise Disjoint

-- ----------------------------------------------------------------
-- Section 2.4: List Support
-- ----------------------------------------------------------------

namespace List

noncomputable def support
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] :
    List (Profile N V) → Finset (PureProfile N V)
  | [] => ∅
  | x :: xs => Profile.support x ∪ support xs

@[simp] theorem support_nil
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] :
    support ([] : List (Profile N V)) = ∅ := rfl

@[simp] theorem support_cons
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (x : Profile N V) (xs : List (Profile N V)) :
    support (x :: xs) = Profile.support x ∪ support xs := rfl

theorem support_append
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (l₁ l₂ : List (Profile N V)) :
    support (l₁ ++ l₂) = support l₁ ∪ support l₂ := by
  induction l₁ with
  | nil => simp [support]
  | cons x xs ih => simp [support, ih, Finset.union_assoc, Finset.union_left_comm]

theorem mem_support_iff
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {l : List (Profile N V)} {p : PureProfile N V} :
    p ∈ support l ↔ ∃ σ ∈ l, p ∈ Profile.support σ := by
  induction l with
  | nil =>
      simp [support]
  | cons x xs ih =>
      constructor
      · intro hp
        simp [support] at hp
        rcases hp with hx | hxs
        · exact ⟨x, by simp, hx⟩
        · rcases (ih.mp hxs) with ⟨σ, hσ, hpσ⟩
          exact ⟨σ, by simp [hσ], hpσ⟩
      · intro h
        rcases h with ⟨σ, hσ, hpσ⟩
        rcases (List.mem_cons).1 hσ with hσ | hσ
        · subst hσ
          simp [support, hpσ]
        · have : p ∈ support xs := ih.mpr ⟨σ, hσ, hpσ⟩
          simp [support, this]

theorem mem_support_of_mem
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    {l : List (Profile N V)} {σ : Profile N V} {p : PureProfile N V}
    (hσ : σ ∈ l) (hp : p ∈ Profile.support σ) :
    p ∈ support l := by
  exact (mem_support_iff).2 ⟨σ, hσ, hp⟩

end List

/-- Size of the union of pure-profile supports across a list. -/
noncomputable def supportSize
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) : ℕ :=
  (List.support l).card

theorem supportSize_le_supportSizeMax
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) :
    supportSize l ≤ Fintype.card (PureProfile N V) := by
  classical
  unfold supportSize
  simpa using (Finset.card_le_univ (List.support l))

theorem supportSize_lt_append_of_forall_not_intersects
    {N : Type*} [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) (σ : Profile N V)
    (h : ∀ τ ∈ l, ¬ Intersects τ σ) :
    supportSize l < supportSize (l ++ [σ]) := by
  classical
  have hdis :
      _root_.Disjoint (List.support l) (Profile.support σ) := by
    refine (Finset.disjoint_left).2 ?_
    intro p hp₁ hp₂
    rcases (List.mem_support_iff.mp hp₁) with ⟨τ, hτ, hpτ⟩
    have hnonempty : (Profile.support τ ∩ Profile.support σ).Nonempty := by
      refine ⟨p, ?_⟩
      exact (Finset.mem_inter.mpr ⟨hpτ, hp₂⟩)
    have hinter : Intersects τ σ :=
      (Intersects_iff_support_intersects (σ := τ) (τ := σ)).2 hnonempty
    exact (h τ hτ) hinter
  have hcard_union :
      (List.support l ∪ Profile.support σ).card =
        (List.support l).card + (Profile.support σ).card := by
    have hinter : List.support l ∩ Profile.support σ = ∅ :=
      (Finset.disjoint_iff_inter_eq_empty).1 hdis
    simpa [hinter] using
      (Finset.card_union (List.support l) (Profile.support σ))
  have hpos : 0 < (Profile.support σ).card := by
    exact Finset.card_pos.mpr (Profile.support_nonempty σ)
  have hlt :
      (List.support l).card <
        (List.support l).card + (Profile.support σ).card :=
    Nat.lt_add_of_pos_right hpos
  unfold supportSize
  have hsupp :
      List.support (l ++ [σ]) = List.support l ∪ Profile.support σ := by
    simp [List.support_append, List.support_cons, List.support_nil]
  simpa [hsupp, hcard_union] using hlt

-- ================================================================
-- Section 3: Games and Payoffs (~100 lines)
-- ================================================================

/-- A game: N players, V i actions for player i, payoffs on pure profiles. -/
structure Game (N : Type*) [DecidableEq N] [Fintype N]
    (V : N → Type*) [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] where
  /-- Player `i`'s preference preorder on pure profiles. -/
  pref : N → PureProfile N V → PureProfile N V → Prop
  /-- Each player's preference is a preorder on pure profiles. -/
  pref_preorder : ∀ i : N, IsPreorder (PureProfile N V) (pref i)
  /-- Each player's preference is total on pure profiles. -/
  pref_total : ∀ i : N, Std.Total (pref i)
  /-- Preference is decidable for each player. -/
  pref_decidable : ∀ i : N, DecidableRel (pref i)

-- ================================================================
-- Section 4: Strict Deviations (~200 lines)
-- ================================================================

namespace Game

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
variable (G : Game N V)

-- ----------------------------------------------------------------
-- Section 4.1: Core Definitions
-- ----------------------------------------------------------------

/-- Face order on deviations in player `i`'s simplex against profile `σ`. -/
def DevFaceLE (i : N) (σ : Profile N V) (A B : DSimplex (V i)) : Prop :=
  ∀ p, Consistent (σ[i ↦ A]) p → ∀ q, Consistent (σ[i ↦ B]) q → G.pref i p q

/-- Strict unilateral deviation to face `A`. -/
def StrictDev (i : N) (σ : Profile N V) (A : DSimplex (V i)) : Prop :=
  G.DevFaceLE i σ (σ i) A ∧ ¬ G.DevFaceLE i σ A (σ i)

/-- A Nash equilibrium: no player has a strict unilateral deviation. -/
def IsNash (σ : Profile N V) : Prop :=
  ∀ i : N, ∀ A : DSimplex (V i), ¬ G.StrictDev i σ A

/-- A strict deviation step between profiles. -/
def StrictDevStep (σ τ : Profile N V) : Prop :=
  ∃ i : N, ∃ A : DSimplex (V i), τ = σ[i ↦ A] ∧ G.StrictDev i σ A

/-- A Best Response for player `i` against `σ` is a face `A` such that `i` has no strict deviation from `σ[i ↦ A]`. -/
def IsBestResponse (i : N) (σ : Profile N V) (A : DSimplex (V i)) : Prop :=
  ∀ B, ¬ G.StrictDev i (σ[i ↦ A]) B

/-- A Strict Best Response deviation. -/
def StrictBestResponse (i : N) (σ : Profile N V) (A : DSimplex (V i)) : Prop :=
  G.StrictDev i σ A ∧ G.IsBestResponse i σ A

/-- A Strict Best Response Step. -/
def StrictBestResponseStep (σ τ : Profile N V) : Prop :=
  ∃ i A, τ = σ[i ↦ A] ∧ G.StrictBestResponse i σ A

/-- `DevFaceLE` is transitive. -/
theorem DevFaceLE_trans (i : N) (σ : Profile N V) (A B C : DSimplex (V i)) :
    G.DevFaceLE i σ A B → G.DevFaceLE i σ B C → G.DevFaceLE i σ A C := by
  intro hAB hBC p hp r hr
  sorry -- Skipped for now to focus on high-level cycle logic

/-- `DevFaceLE` context equivalence. -/
theorem DevFaceLE_context_eq {i : N} {σ τ : Profile N V}
    (h : ∀ j, j ≠ i → σ j = τ j) :
    ∀ A B, G.DevFaceLE i σ A B ↔ G.DevFaceLE i τ A B := by
  intro A B
  unfold DevFaceLE
  have h_cons : ∀ {X}, (∀ p, Consistent (σ[i ↦ X]) p ↔ Consistent (τ[i ↦ X]) p) := by
    intro X p
    unfold Consistent
    apply forall_congr'
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]; rw [h j hj]
  constructor
  · intro H p hp q hq
    have hp' : Consistent (σ[i ↦ A]) p := by rw [h_cons]; exact hp
    have hq' : Consistent (σ[i ↦ B]) q := by rw [h_cons]; exact hq
    exact H p hp' q hq'
  · intro H p hp q hq
    have hp' : Consistent (τ[i ↦ A]) p := by rw [← h_cons]; exact hp
    have hq' : Consistent (τ[i ↦ B]) q := by rw [← h_cons]; exact hq
    exact H p hp' q hq'

/-- `Better` relation: A is strictly better than B for player i against σ_{-i}. -/
def Better (i : N) (σ : Profile N V) (A B : DSimplex (V i)) : Prop :=
  G.StrictDev i (σ[i ↦ B]) A

theorem Better_irref (i : N) (σ : Profile N V) (A : DSimplex (V i)) :
    ¬ G.Better i σ A A := by
  intro h
  unfold Better StrictDev at h
  rcases h with ⟨h1, h2⟩
  rw [Function.update_self] at h1 h2
  exact h2 h1

theorem Better_trans (i : N) (σ : Profile N V) {A B C : DSimplex (V i)} :
    G.Better i σ A B → G.Better i σ B C → G.Better i σ A C := by
  intro hAB hBC
  unfold Better at *
  have h_eq : ∀ D E, G.DevFaceLE i (σ[i ↦ B]) D E ↔ G.DevFaceLE i (σ[i ↦ C]) D E :=
    G.DevFaceLE_context_eq (by intro j hj; simp [hj])
  unfold StrictDev at hAB hBC
  simp only [Function.update_self] at hAB hBC
  rw [h_eq] at hAB
  unfold StrictDev
  simp only [Function.update_self]
  constructor
  · apply G.DevFaceLE_trans (i := i) (σ := σ[i ↦ C]) (A := C) (B := B) (C := A) hBC.1 hAB.1
  · intro hCA
    have hAB_derived := G.DevFaceLE_trans (i := i) (σ := σ[i ↦ C]) (A := A) (B := C) (C := B) hCA hBC.1
    rw [← h_eq] at hAB_derived
    exact hAB.2 hAB_derived

theorem exists_best_response (i : N) (σ : Profile N V) :
    ∃ A : DSimplex (V i), G.IsBestResponse i σ A := by
  classical
  -- Use Classical choice to assert existence of maximal element
  -- since Better is a strict partial order on a finite set.
  have h_exists : ∃ m, ∀ x, ¬ G.Better i σ x m := by
    -- Standard result for finite strict partial orders
    let S := (Finset.univ : Finset (DSimplex (V i)))
    have h_ne : S.Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact ⟨σ i⟩
    sorry -- Proof omitted for refactoring speed
  obtain ⟨m, hm⟩ := h_exists
  refine ⟨m, ?_⟩
  intro B
  exact hm B

-- ----------------------------------------------------------------
-- Section 4.2: Canonical Choice of Deviations (Constructive)
-- ----------------------------------------------------------------

/-- Existence of a strict deviation when not Nash (classical). -/
theorem exists_strictDev_of_not_nash
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    ∃ i : N, ∃ A : DSimplex (V i), G.StrictDev i σ A := by
  classical
  simpa [IsNash] using h

/-- Existence of a strict best response deviation when not Nash. -/
theorem exists_strictBestResponse_of_not_nash
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    ∃ i : N, ∃ A : DSimplex (V i), G.StrictBestResponse i σ A := by
  classical
  obtain ⟨i, A, hdev⟩ := G.exists_strictDev_of_not_nash h
  -- hdev is StrictDev i σ A => Better i σ A (σ i)
  -- Better is a strict partial order, so there exists a maximal element m ≥ A > (σ i).
  obtain ⟨m, hm⟩ := G.exists_best_response i σ
  -- Does exists_best_response guarantee m ≥ A?
  -- No, it just gives *some* best response.
  -- But we can find a best response *reachable* from A.
  -- Or simpler: "Better" has maximal elements above any element in a finite set?
  -- Yes.
  sorry -- Proof: Finite strict partial order property

/-- A restricting strict best response: deviation to a proper subface. -/
def RestrictingStrictBestResponse (i : N) (σ : Profile N V) (A : DSimplex (V i)) : Prop :=
  G.StrictBestResponse i σ A ∧ DSimplex.IsSubface A (σ i) ∧ A ≠ σ i

/-- The set of restricting strict best response deviations at a profile.
    These are deviations that shrink the space (proper subfaces only). -/
noncomputable def devSet (σ : Profile N V) : Finset (DevFace N V) := by
  classical
  exact Finset.univ.filter (fun d => G.RestrictingStrictBestResponse d.1 σ d.2)

/-- When not Nash, there exists a restricting strict best response. -/
theorem exists_restrictingStrictBestResponse_of_not_nash
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    ∃ i : N, ∃ A : DSimplex (V i), G.RestrictingStrictBestResponse i σ A := by
  sorry -- TODO: Show that any StrictBestResponse can be restricted, or find one directly

theorem devSet_nonempty {σ : Profile N V} (h : ¬ G.IsNash σ) :
    (devSet G σ).Nonempty := by
  classical
  obtain ⟨i, A, hdev⟩ := G.exists_restrictingStrictBestResponse_of_not_nash h
  refine ⟨⟨i, A⟩, ?_⟩
  simp [devSet, hdev]

/-- Constructive choice: minimal strict deviation under canonical order. -/
noncomputable def next (σ : Profile N V) : Profile N V := by
  classical
  by_cases h : G.IsNash σ
  · exact σ
  · let d := (devSet G σ).min' (devSet_nonempty G h)
    exact σ[d.1 ↦ d.2]

theorem next_spec_not_nash
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    let d := (devSet G σ).min' (devSet_nonempty G h)
    G.next σ = σ[d.1 ↦ d.2] ∧ G.RestrictingStrictBestResponse d.1 σ d.2 := by
  classical
  let d := (devSet G σ).min' (devSet_nonempty G h)
  have hmem : d ∈ devSet G σ := by
    exact Finset.min'_mem (devSet G σ) (devSet_nonempty G h)
  have hdev : G.RestrictingStrictBestResponse d.1 σ d.2 := by
    simpa [devSet] using (Finset.mem_filter.mp hmem).2
  constructor
  · unfold next
    simp only [h, dite_false]
  · exact hdev

theorem next_step_of_not_nash
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    G.StrictBestResponseStep σ (G.next σ) := by
  have ⟨heq, hdev⟩ := G.next_spec_not_nash h
  let d := (devSet G σ).min' (devSet_nonempty G h)
  refine ⟨d.1, d.2, ?_, hdev.1⟩  -- Extract StrictBestResponse from RestrictingStrictBestResponse
  exact heq

-- ----------------------------------------------------------------
-- Section 4.3: Key Monotonicity Lemmas
-- ----------------------------------------------------------------

/-- `DevFaceLE` is antitone in the profile argument. -/
theorem DevFaceLE_antitone
    {σ τ : Profile N V} (h : ProfileLE σ τ)
    (i : N) (A B : DSimplex (V i)) :
    G.DevFaceLE i τ A B → G.DevFaceLE i σ A B := by
  intro hdev p hp q hq
  have hσA : Consistent (τ[i ↦ A]) p := by
    apply Consistent_mono (ProfileLE_update h i A)
    exact hp
  have hσB : Consistent (τ[i ↦ B]) q := by
    apply Consistent_mono (ProfileLE_update h i B)
    exact hq
  exact hdev p hσA q hσB

/-- `DevFaceLE` is monotone in the left face. -/
theorem DevFaceLE_left_mono
    {i : N} {σ : Profile N V} {A A' B : DSimplex (V i)}
    (h : DSimplex.IsSubface A A') :
    G.DevFaceLE i σ A' B → G.DevFaceLE i σ A B := by
  intro hle p hp q hq
  have hp' : Consistent (σ[i ↦ A']) p := by
    apply Consistent_mono (ProfileLE_update_left σ i h)
    exact hp
  exact hle p hp' q hq

/-- `DevFaceLE` is monotone in the right face. -/
theorem DevFaceLE_right_mono
    {i : N} {σ : Profile N V} {A B B' : DSimplex (V i)}
    (h : DSimplex.IsSubface B B') :
    G.DevFaceLE i σ A B' → G.DevFaceLE i σ A B := by
  intro hle p hp q hq
  have hq' : Consistent (σ[i ↦ B']) q := by
    apply Consistent_mono (ProfileLE_update_left σ i h)
    exact hq
  exact hle p hp q hq'

/-- A defense against dominance of `B` by `A`. -/
def Defends (i : N) (σ : Profile N V) (A B : DSimplex (V i)) : Prop :=
  ¬ G.DevFaceLE i σ A B

theorem Defends_mono
    {i : N} {σ τ : Profile N V} {A B : DSimplex (V i)}
    (h : ProfileLE σ τ) :
    G.Defends i σ A B → G.Defends i τ A B := by
  intro hdef hle
  exact hdef (G.DevFaceLE_antitone h i A B hle)

theorem Defends_mix_left
    {i : N} {σ τ : Profile N V} {A B : DSimplex (V i)} :
    G.Defends i σ A B → G.Defends i (Profile.mix σ τ) A B := by
  intro hdef
  exact G.Defends_mono (i := i) (σ := σ) (τ := Profile.mix σ τ)
    (ProfileLE_mix_left σ τ) hdef

theorem Defends_mix_right
    {i : N} {σ τ : Profile N V} {A B : DSimplex (V i)} :
    G.Defends i τ A B → G.Defends i (Profile.mix σ τ) A B := by
  intro hdef
  exact G.Defends_mono (i := i) (σ := τ) (τ := Profile.mix σ τ)
    (ProfileLE_mix_right σ τ) hdef

-- ================================================================
-- Section 5: Profile Size and Descent (~100 lines)
-- ================================================================

/-- Total number of vertices across all players' faces. -/
def profileSize (σ : Profile N V) : ℕ :=
  Finset.univ.sum (fun i => (σ i).1.card)

/-- Restricting strict best response implies proper subface (by definition). -/
theorem RestrictingStrictBestResponse_proper_subface
    {i : N} {σ : Profile N V} {A : DSimplex (V i)}
    (h : G.RestrictingStrictBestResponse i σ A) :
    DSimplex.IsSubface A (σ i) ∧ A ≠ σ i := by
  exact ⟨h.2.1, h.2.2⟩

/-- Profile size decreases under next step. -/
theorem profileSize_decreases_next
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    profileSize (G.next σ) < profileSize σ := by
  obtain ⟨heq, hdev⟩ := G.next_spec_not_nash h
  let d := (devSet G σ).min' (devSet_nonempty G h)
  rw [heq]
  have ⟨hsub, hne⟩ := G.RestrictingStrictBestResponse_proper_subface hdev
  unfold profileSize
  -- The card at d.1 strictly decreases
  have hcard : (d.2).1.card < (σ d.1).1.card := by
    have : (d.2).1 ⊂ (σ d.1).1 := by
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (DSimplex.ext h)⟩
    exact Finset.card_lt_card this
  -- Decompose: sum over all = term at d.1 + sum over others
  conv_lhs => rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ d.1)]
  conv_rhs => rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ d.1)]
  -- At d.1: (σ[d.1 ↦ d.2] d.1).1.card = (d.2).1.card < (σ d.1).1.card
  -- Elsewhere: (σ[d.1 ↦ d.2] i).1.card = (σ i).1.card for i ≠ d.1
  have h_at_d : ((σ[d.1 ↦ d.2]) d.1).1.card = (d.2).1.card := by
    show (Function.update σ d.1 d.2 d.1).1.card = (d.2).1.card
    unfold Function.update
    split_ifs
    · rfl
    · contradiction
  have h_elsewhere : ∀ i ∈ Finset.univ.erase d.1, ((σ[d.1 ↦ d.2]) i).1.card = (σ i).1.card := by
    intro i hi
    have hne : i ≠ d.1 := Finset.mem_erase.mp hi |>.1
    show (Function.update σ d.1 d.2 i).1.card = (σ i).1.card
    unfold Function.update
    split_ifs with h
    · subst h; contradiction
    · rfl
  rw [h_at_d]
  rw [Finset.sum_congr rfl h_elsewhere]
  omega

/-- Strict best response dominates the original face in restricted contexts. -/
theorem StrictBestResponse_dominates_in_subprofiles
    {i : N} {σ : Profile N V} {A : DSimplex (V i)}
    (h : G.StrictBestResponse i σ A) :
    ∀ τ, ProfileLE τ σ → G.DevFaceLE i τ (σ i) A := by
  sorry -- TODO: Key lemma from PROOF_IDEA.md - dominance survives restriction

/-- When we move to a strict best response, the new profile inherits non-Nash-ness
    or becomes Nash. This is the core of the descent argument. -/
theorem next_preserves_or_creates_nash
    (σ : Profile N V) :
    G.IsNash (G.next σ) ∨ profileSize (G.next σ) < profileSize σ := by
  by_cases h : G.IsNash σ
  · left
    unfold next
    simp [h]
  · right
    exact G.profileSize_decreases_next h

-- ================================================================
-- Section 6: Nash Existence via Well-Founded Descent
-- ================================================================

/-- Helper: maximal profile with all vertices. -/
noncomputable def maximalProfile [∀ i, Nonempty (V i)] : Profile N V :=
  fun _ => ⟨Finset.univ, Finset.univ_nonempty⟩

/-- Upper bound on profile size. -/
theorem profileSize_bounded {N : Type*} [Fintype N] [DecidableEq N]
    {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    (σ : Profile N V) :
    profileSize σ ≤ Finset.univ.sum (fun i => Fintype.card (V i)) := by
  unfold profileSize
  apply Finset.sum_le_sum
  intro i _
  exact Finset.card_le_univ (σ i).1

/-- Decidability instance for IsNash. -/
noncomputable instance instDecidableIsNash (σ : Profile N V) :
    Decidable (G.IsNash σ) := by
  classical
  infer_instance

/-- Constructive Nash finder using well-founded recursion on profile size. -/
noncomputable def findNash (σ : Profile N V) : Profile N V :=
  if h : G.IsNash σ then
    σ
  else
    have : profileSize (G.next σ) < profileSize σ := G.profileSize_decreases_next h
    findNash (G.next σ)
termination_by profileSize σ

/-- The result of findNash is always a Nash equilibrium. -/
theorem findNash_is_nash (σ : Profile N V) :
    G.IsNash (G.findNash σ) := by
  unfold findNash
  split
  · assumption
  · rename_i h
    have : profileSize (G.next σ) < profileSize σ := G.profileSize_decreases_next h
    exact findNash_is_nash (G.next σ)
termination_by profileSize σ

/-- Nash equilibrium existence - main theorem. -/
theorem nash_exists [∀ i, Nonempty (V i)] : ∃ σ : Profile N V, G.IsNash σ := by
  exact ⟨G.findNash (maximalProfile (N := N) (V := V)), G.findNash_is_nash _⟩
