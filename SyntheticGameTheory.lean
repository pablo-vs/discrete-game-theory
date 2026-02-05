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

-- ----------------------------------------------------------------
-- Section 4.2: Canonical Choice of Deviations (Constructive)
-- ----------------------------------------------------------------

/-- Existence of a strict deviation when not Nash (classical). -/
theorem exists_strictDev_of_not_nash
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    ∃ i : N, ∃ A : DSimplex (V i), G.StrictDev i σ A := by
  classical
  simpa [IsNash] using h

/-- The set of strict deviation faces at a profile. -/
noncomputable def devSet (σ : Profile N V) : Finset (DevFace N V) := by
  classical
  exact Finset.univ.filter (fun d => G.StrictDev d.1 σ d.2)

theorem devSet_nonempty {σ : Profile N V} (h : ¬ G.IsNash σ) :
    (devSet G σ).Nonempty := by
  classical
  obtain ⟨i, A, hdev⟩ := G.exists_strictDev_of_not_nash (σ := σ) h
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
    G.next σ = σ[d.1 ↦ d.2] ∧ G.StrictDev d.1 σ d.2 := by
  classical
  let d := (devSet G σ).min' (devSet_nonempty G h)
  have hmem : d ∈ devSet G σ := by
    exact Finset.min'_mem (devSet G σ) (devSet_nonempty G h)
  have hdev : G.StrictDev d.1 σ d.2 := by
    simpa [devSet] using (Finset.mem_filter.mp hmem).2
  constructor
  · unfold next
    simp only [h, dite_false]
  · exact hdev

theorem next_step_of_not_nash
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    G.StrictDevStep σ (G.next σ) := by
  have ⟨heq, hdev⟩ := G.next_spec_not_nash h
  let d := (devSet G σ).min' (devSet_nonempty G h)
  refine ⟨d.1, d.2, ?_, hdev⟩
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
-- Section 5: Paths and Defense Lemmas (~250 lines)
-- ================================================================

-- ----------------------------------------------------------------
-- Section 5.1: Strict Deviation Paths
-- ----------------------------------------------------------------

/-- A path of strict deviation steps. -/
def StrictDevPath : List (Profile N V) → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => G.StrictDevStep x y ∧ StrictDevPath (y :: xs)

theorem StrictDevPath_head_step
    {x y : Profile N V} {xs : List (Profile N V)}
    (h : G.StrictDevPath (x :: y :: xs)) : G.StrictDevStep x y := by
  cases h with
  | intro hstep _ => exact hstep

/-- A strict deviation cycle: a nonempty list with strict steps between
    consecutive elements and last-to-head. -/
def StrictDevCycle (l : List (Profile N V)) : Prop :=
  ∃ x xs, l = x :: xs ∧
    G.StrictDevPath l ∧
    G.StrictDevStep ((x :: xs).getLast (by simp)) x

-- ----------------------------------------------------------------
-- Section 5.2: Defense Lemmas (Core Insight)
-- ----------------------------------------------------------------

/-- If player `i` strictly deviates from `C` to a subface `A`, then within any
    subprofile `σ ≤ C` that keeps `i` at `A`, player `i` cannot strictly deviate
    to any subface of `C i`. -/
theorem not_strictDev_subface_of_strictDev
    {i : N} {C σ : Profile N V} {A B : DSimplex (V i)}
    (hdev : G.StrictDev i C A)
    (hσC : ProfileLE σ C) (hσi : σ i = A)
    (hB : DSimplex.IsSubface B (C i)) :
    ¬ G.StrictDev i σ B := by
  intro h
  have hle_C : G.DevFaceLE i C (C i) A := hdev.1
  have hle_BA_C : G.DevFaceLE i C B A :=
    G.DevFaceLE_left_mono (i := i) (σ := C) (A := B) (A' := C i) (B := A) hB hle_C
  have hle_BA_σ : G.DevFaceLE i σ B A :=
    G.DevFaceLE_antitone (σ := σ) (τ := C) hσC i B A hle_BA_C
  have hle_BA_σ' : G.DevFaceLE i σ B (σ i) := by
    simpa [hσi] using hle_BA_σ
  exact h.2 hle_BA_σ'

theorem not_devfaceLE_mixList_of_strictDev
    {i : N} {σ τ : Profile N V} {A : DSimplex (V i)}
    {l : List (Profile N V)} (hne : l ≠ [])
    (hτ : τ = σ[i ↦ A]) (hdev : G.StrictDev i σ A)
    (hσ : σ ∈ l) (hτmem : τ ∈ l) :
    ¬ G.DevFaceLE i (Profile.mixList l hne) ((Profile.mixList l hne) i) (σ i) := by
  let M := Profile.mixList l hne
  have hσM : ProfileLE σ M := ProfileLE_mixList_of_mem (l := l) hne hσ
  have hτM : ProfileLE τ M := ProfileLE_mixList_of_mem (l := l) hne hτmem
  have hBM : DSimplex.IsSubface A (M i) := by
    have hsub : DSimplex.IsSubface (τ i) (M i) := hτM i
    simpa [hτ] using hsub
  have hdef : G.Defends i M A (σ i) := by
    have hdef0 : G.Defends i σ A (σ i) := hdev.2
    exact G.Defends_mono (i := i) (σ := σ) (τ := M) hσM hdef0
  intro hle
  have hle' : G.DevFaceLE i M A (σ i) :=
    G.DevFaceLE_left_mono (i := i) (σ := M) (A := A) (A' := M i) (B := σ i) hBM hle
  exact hdef hle'

theorem not_strictDev_mixList_of_strictDev
    {i : N} {σ τ : Profile N V} {A : DSimplex (V i)}
    {l : List (Profile N V)} (hne : l ≠ [])
    (hτ : τ = σ[i ↦ A]) (hdev : G.StrictDev i σ A)
    (hσ : σ ∈ l) (hτmem : τ ∈ l) :
    ¬ G.StrictDev i (Profile.mixList l hne) (σ i) := by
  intro h
  exact (G.not_devfaceLE_mixList_of_strictDev (i := i) (σ := σ) (τ := τ)
    (A := A) (l := l) hne hτ hdev hσ hτmem) h.1

theorem not_strictDev_mixList_of_step_in_list
    {σ τ : Profile N V} {l : List (Profile N V)} (hne : l ≠ [])
    (hstep : G.StrictDevStep σ τ) (hσ : σ ∈ l) (hτ : τ ∈ l) :
    ∃ i : N, ¬ G.StrictDev i (Profile.mixList l hne) (σ i) := by
  rcases hstep with ⟨i, A, hτ', hdev⟩
  refine ⟨i, ?_⟩
  exact G.not_strictDev_mixList_of_strictDev (i := i) (σ := σ) (τ := τ)
    (A := A) (l := l) hne hτ' hdev hσ hτ

theorem not_strictDev_mixList_of_path_head
    {x y : Profile N V} {xs : List (Profile N V)}
    (hpath : G.StrictDevPath (x :: y :: xs)) :
    ∃ i : N, ¬ G.StrictDev i
      (Profile.mixList (x :: y :: xs) (by simp)) (x i) := by
  have hstep : G.StrictDevStep x y := G.StrictDevPath_head_step hpath
  have hx : x ∈ (x :: y :: xs) := by simp
  have hy : y ∈ (x :: y :: xs) := by simp
  exact G.not_strictDev_mixList_of_step_in_list (l := x :: y :: xs)
    (hne := by simp) hstep hx hy

-- ----------------------------------------------------------------
-- Section 5.3: Frozen Player Lemmas
-- ----------------------------------------------------------------

theorem StrictDevStep_unique_player
    {σ τ : Profile N V} {i j : N}
    {A : DSimplex (V i)} {B : DSimplex (V j)}
    (hτi : τ = σ[i ↦ A])
    (hτj : τ = σ[j ↦ B]) (hdev_j : G.StrictDev j σ B) :
    i = j := by
  by_contra hne
  have h1 : τ j = σ j := by
    have hji : j ≠ i := by exact ne_comm.mp hne
    simp [hτi, hji]
  have h2 : τ j = B := by
    simp [hτj]
  have hB : B = σ j := by
    calc
      B = τ j := by simp [h2]
      _ = σ j := h1
  have hdev' : G.DevFaceLE j σ (σ j) (σ j) := by
    simpa [hB] using hdev_j.1
  have hnot : ¬ G.DevFaceLE j σ (σ j) (σ j) := by
    simpa [hB] using hdev_j.2
  exact hnot hdev'

/-- If player `i` deviates from `C` to `A`, then any later strict deviation
    inside `C` from a profile that keeps `i` at `A` must be by a different player. -/
theorem StrictDevStep_player_ne_of_frozen
    {i : N} {C σ τ : Profile N V} {A : DSimplex (V i)}
    (hdev : G.StrictDev i C A)
    (hσC : ProfileLE σ C) (hσi : σ i = A)
    (hτC : ProfileLE τ C)
    (hstep : G.StrictDevStep σ τ) :
    ∃ j : N, j ≠ i ∧ ∃ B : DSimplex (V j), τ = σ[j ↦ B] ∧ G.StrictDev j σ B := by
  rcases hstep with ⟨j, B, hτ, hdev'⟩
  have hj : j ≠ i := by
    by_cases hji : j = i
    · subst j
      have hB : DSimplex.IsSubface B (C i) := by
        have hsub : DSimplex.IsSubface (τ i) (C i) := hτC i
        simpa [hτ] using hsub
      have hcontra :
          ¬ G.StrictDev i σ B :=
        G.not_strictDev_subface_of_strictDev
          (i := i) (C := C) (σ := σ) (A := A) (B := B)
          hdev hσC hσi hB
      exact (hcontra hdev').elim
    · exact hji
  exact ⟨j, hj, B, hτ, hdev'⟩

theorem StrictDevStep_player_ne_of_frozen_unique
    {i : N} {C σ τ : Profile N V} {A : DSimplex (V i)}
    (hdev : G.StrictDev i C A)
    (hσC : ProfileLE σ C) (hσi : σ i = A)
    (hτC : ProfileLE τ C)
    (hstep : G.StrictDevStep σ τ) :
    ∀ {j : N} {B : DSimplex (V j)},
      τ = σ[j ↦ B] → G.StrictDev j σ B → j ≠ i := by
  intro j B hτ hdevj
  obtain ⟨j', hj', B', hτ', hdev'⟩ :=
    G.StrictDevStep_player_ne_of_frozen (i := i) (C := C) (σ := σ) (τ := τ) (A := A)
      hdev hσC hσi hτC hstep
  have hj_eq : j = j' :=
    G.StrictDevStep_unique_player (σ := σ) (τ := τ) (i := j) (j := j')
      (A := B) (B := B') hτ hτ' hdev'
  simpa [hj_eq] using hj'

theorem StrictDev_defends
    {i : N} {σ : Profile N V} {A : DSimplex (V i)} :
    G.StrictDev i σ A → G.Defends i σ A (σ i) := by
  intro h
  exact h.2

-- ================================================================
-- Section 6: Nash Algorithm (~200 lines)
-- ================================================================

-- ----------------------------------------------------------------
-- Section 6.1: List Utilities
-- ----------------------------------------------------------------

namespace List

def splitOnFirst {α : Type*} (p : α → Prop) [DecidablePred p] :
    List α → List α × List α
  | [] => ([], [])
  | x :: xs =>
      if _ : p x then
        ([], x :: xs)
      else
        let (pref, suff) := splitOnFirst p xs
        (x :: pref, suff)

theorem splitOnFirst_eq
    {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) :
    let r := splitOnFirst p l; l = r.1 ++ r.2 := by
  induction l with
  | nil =>
      simp [splitOnFirst]
  | cons x xs ih =>
      by_cases hx : p x
      · simp [splitOnFirst, hx]
      ·
        cases h : splitOnFirst p xs with
        | mk pref suff =>
            have ih' : xs = pref ++ suff := by
              simpa [h] using ih
            have hx' : x :: xs = (x :: pref) ++ suff := by
              calc
                x :: xs = x :: (pref ++ suff) := by simp [ih']
                _ = (x :: pref) ++ suff := by simp
            simpa [splitOnFirst, hx, h] using hx'

theorem splitOnFirst_pref_no
    {α : Type*} (p : α → Prop) [DecidablePred p] :
    ∀ l, ∀ x ∈ (splitOnFirst p l).1, ¬ p x := by
  intro l
  induction l with
  | nil =>
      intro x hx
      intro hx'
      have : False := by
        simpa [splitOnFirst] using hx
      exact this.elim
  | cons a xs ih =>
      by_cases ha : p a
      · intro x hx
        intro hx'
        have : False := by
          simpa [splitOnFirst, ha] using hx
        exact this.elim
      ·
        intro x hx
        cases hxs : splitOnFirst p xs with
        | mk pref suff =>
            have hx' : x = a ∨ x ∈ pref := by
              simpa [splitOnFirst, ha, hxs] using hx
            rcases hx' with hx' | hx'
            · subst hx'
              exact ha
            ·
              have hpref : ∀ x ∈ pref, ¬ p x := by
                simpa [hxs] using ih
              exact hpref x hx'

end List

theorem append_singleton_ne_nil {α : Type*} (l : List α) (x : α) :
    l ++ [x] ≠ [] := by
  simp

noncomputable def mixSuffix
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)]
    (x : Profile N V) (xs : List (Profile N V)) (σ : Profile N V) :
    Profile N V :=
  Profile.mixList ((x :: xs) ++ [σ]) (append_singleton_ne_nil (x :: xs) σ)

theorem Intersects_mixSuffix
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)]
    (x : Profile N V) (xs : List (Profile N V)) (σ : Profile N V) :
    Intersects (mixSuffix x xs σ) σ := by
  have hmem : σ ∈ (x :: xs) ++ [σ] := by
    simp
  have hle : ProfileLE σ (mixSuffix x xs σ) := by
    simpa [mixSuffix] using
      (ProfileLE_mixList_of_mem (l := (x :: xs) ++ [σ])
        (hne := append_singleton_ne_nil (x :: xs) σ) hmem)
  exact Intersects_symm (Intersects_of_ProfileLE hle)

theorem mixSuffix_mem_suffix_of_split
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)]
    {l : List (Profile N V)} {σ : Profile N V}
    {pref : List (Profile N V)} {x : Profile N V} {xs : List (Profile N V)}
    [DecidablePred (fun τ => Intersects τ σ)]
    (h : List.splitOnFirst (fun τ => Intersects τ σ) l = (pref, x :: xs))
    (hm : mixSuffix x xs σ ∈ l) :
    mixSuffix x xs σ ∈ x :: xs := by
  classical
  have h1 : (List.splitOnFirst (fun τ => Intersects τ σ) l).1 = pref := by
    simpa [h]
  have h2 : (List.splitOnFirst (fun τ => Intersects τ σ) l).2 = x :: xs := by
    simpa [h]
  have hsplit : l = pref ++ (x :: xs) := by
    have hsplit0 := List.splitOnFirst_eq (p := fun τ => Intersects τ σ) l
    simpa [h1, h2] using hsplit0
  have hno : ∀ τ ∈ pref, ¬ Intersects τ σ := by
    have hno0 :
        ∀ τ ∈ (List.splitOnFirst (fun τ => Intersects τ σ) l).1,
          ¬ Intersects τ σ :=
      List.splitOnFirst_pref_no (p := fun τ => Intersects τ σ) l
    simpa [h1] using hno0
  have hinter : Intersects (mixSuffix x xs σ) σ :=
    Intersects_mixSuffix x xs σ
  have hnotpref : mixSuffix x xs σ ∉ pref := by
    intro hmem
    exact (hno _ hmem) hinter
  have hm' : mixSuffix x xs σ ∈ pref ++ (x :: xs) := by
    simpa [hsplit] using hm
  rcases List.mem_append.mp hm' with hmem | hmem
  · exact (hnotpref hmem).elim
  · exact hmem

-- ----------------------------------------------------------------
-- Section 6.2: Collapse Lemmas
-- ----------------------------------------------------------------

noncomputable def collapseAppend
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) (σ : Profile N V) : List (Profile N V) := by
  classical
  exact
    match List.splitOnFirst (fun τ => Intersects τ σ) l with
    | (pref, []) => l ++ [σ]
    | (pref, x :: xs) =>
        if hm : mixSuffix x xs σ ∈ l then
          l ++ [σ]
        else
          pref ++ [mixSuffix x xs σ]

theorem collapseAppend_ne_nil
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) (σ : Profile N V) :
    collapseAppend l σ ≠ [] := by
  classical
  cases h : List.splitOnFirst (fun τ => Intersects τ σ) l with
  | mk pref suff =>
      cases suff with
      | nil =>
          simp [collapseAppend, h]
      | cons x xs =>
          by_cases hm :
              mixSuffix x xs σ ∈ l
          · simp [collapseAppend, h, hm]
          · simp [collapseAppend, h, hm]

theorem collapseAppend_forall_le
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) (σ : Profile N V) :
    ∀ τ ∈ l ++ [σ],
      ProfileLE τ (Profile.mixList (collapseAppend l σ) (collapseAppend_ne_nil l σ)) := by
  classical
  cases h : List.splitOnFirst (fun τ => Intersects τ σ) l with
  | mk pref suff =>
      have hsplit : l = pref ++ suff := by
        simpa [h] using
          (List.splitOnFirst_eq (p := fun τ => Intersects τ σ) l)
      cases suff with
      | nil =>
          intro τ hτ
          have hne_c : collapseAppend l σ ≠ [] := collapseAppend_ne_nil l σ
          have hmem : τ ∈ collapseAppend l σ := by
            simpa [collapseAppend, h] using hτ
          exact ProfileLE_mixList_of_mem (l := collapseAppend l σ) (hne := hne_c) hmem
      | cons x xs =>
          by_cases hm :
              mixSuffix x xs σ ∈ l
          · intro τ hτ
            have hne_c : collapseAppend l σ ≠ [] := collapseAppend_ne_nil l σ
            have hmem : τ ∈ collapseAppend l σ := by
              simpa [collapseAppend, h, hm] using hτ
            exact ProfileLE_mixList_of_mem (l := collapseAppend l σ) (hne := hne_c) hmem
          · intro τ hτ
            have hne_c : collapseAppend l σ ≠ [] := collapseAppend_ne_nil l σ
            have hmem_c :
                mixSuffix x xs σ ∈
                  collapseAppend l σ := by
              simp [collapseAppend, h, hm]
            have hτ' : τ ∈ pref ++ (x :: xs) ++ [σ] := by
              simpa [hsplit, List.append_assoc] using hτ
            rcases (List.mem_append.mp hτ') with hτpref_or | hτσ
            · rcases (List.mem_append.mp hτpref_or) with hτpref | hτxs
              · have hmem : τ ∈ collapseAppend l σ := by
                  simp [collapseAppend, h, hm, hτpref]
                exact ProfileLE_mixList_of_mem (l := collapseAppend l σ) (hne := hne_c) hmem
              · have hτsuff : τ ∈ (x :: xs) ++ [σ] := by
                  exact List.mem_append.mpr (Or.inl hτxs)
                have hτle1 :
                    ProfileLE τ (mixSuffix x xs σ) := by
                  simpa [mixSuffix] using
                    (ProfileLE_mixList_of_mem (l := (x :: xs) ++ [σ])
                      (hne := append_singleton_ne_nil (x :: xs) σ) hτsuff)
                have hτle2 :
                    ProfileLE (mixSuffix x xs σ)
                      (Profile.mixList (collapseAppend l σ) hne_c) :=
                  ProfileLE_mixList_of_mem (l := collapseAppend l σ) (hne := hne_c) hmem_c
                exact ProfileLE_trans hτle1 hτle2
            · have hτsuff : τ ∈ (x :: xs) ++ [σ] := by
                exact List.mem_append.mpr (Or.inr hτσ)
              have hτle1 :
                  ProfileLE τ (mixSuffix x xs σ) := by
                simpa [mixSuffix] using
                  (ProfileLE_mixList_of_mem (l := (x :: xs) ++ [σ])
                    (hne := append_singleton_ne_nil (x :: xs) σ) hτsuff)
              have hτle2 :
                  ProfileLE (mixSuffix x xs σ)
                    (Profile.mixList (collapseAppend l σ) hne_c) :=
                ProfileLE_mixList_of_mem (l := collapseAppend l σ) (hne := hne_c) hmem_c
              exact ProfileLE_trans hτle1 hτle2

theorem supportSize_le_collapseAppend
    {N : Type*} [DecidableEq N] [Fintype N]
    {V : N → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) (σ : Profile N V) :
    supportSize (l ++ [σ]) ≤ supportSize (collapseAppend l σ) := by
  classical
  unfold supportSize
  apply Finset.card_le_card
  intro p hp
  rcases (List.mem_support_iff.mp hp) with ⟨τ, hτ, hpτ⟩
  cases h : List.splitOnFirst (fun τ => Intersects τ σ) l with
  | mk pref suff =>
      have hsplit : l = pref ++ suff := by
        simpa [h] using
          (List.splitOnFirst_eq (p := fun τ => Intersects τ σ) l)
      cases suff with
      | nil =>
          have hmem : τ ∈ collapseAppend l σ := by
            simpa [collapseAppend, h] using hτ
          exact List.mem_support_of_mem hmem hpτ
      | cons x xs =>
          by_cases hm :
              mixSuffix x xs σ ∈ l
          · have hmem : τ ∈ collapseAppend l σ := by
              simpa [collapseAppend, h, hm] using hτ
            exact List.mem_support_of_mem hmem hpτ
          · have hτ' : τ ∈ pref ++ (x :: xs) ++ [σ] := by
              simpa [hsplit, List.append_assoc] using hτ
            rcases (List.mem_append.mp hτ') with hτpref_or | hτσ
            · rcases (List.mem_append.mp hτpref_or) with hτpref | hτxs
              · have hmem : τ ∈ collapseAppend l σ := by
                  simp [collapseAppend, h, hm, hτpref]
                exact List.mem_support_of_mem hmem hpτ
              · have hτsuff : τ ∈ (x :: xs) ++ [σ] := by
                  exact List.mem_append.mpr (Or.inl hτxs)
                have hle :
                    ProfileLE τ (mixSuffix x xs σ) := by
                  simpa [mixSuffix] using
                    (ProfileLE_mixList_of_mem (l := (x :: xs) ++ [σ])
                      (hne := append_singleton_ne_nil (x :: xs) σ) hτsuff)
                have hp' :
                    p ∈ Profile.support (mixSuffix x xs σ) :=
                  (Profile.support_subset_of_le hle) hpτ
                have hmem :
                    mixSuffix x xs σ ∈ collapseAppend l σ := by
                  simp [collapseAppend, h, hm]
                exact List.mem_support_of_mem hmem hp'
            · have hτsuff : τ ∈ (x :: xs) ++ [σ] := by
                exact List.mem_append.mpr (Or.inr hτσ)
              have hle :
                  ProfileLE τ (mixSuffix x xs σ) := by
                simpa [mixSuffix] using
                  (ProfileLE_mixList_of_mem (l := (x :: xs) ++ [σ])
                    (hne := append_singleton_ne_nil (x :: xs) σ) hτsuff)
              have hp' :
                  p ∈ Profile.support (mixSuffix x xs σ) :=
                (Profile.support_subset_of_le hle) hpτ
              have hmem :
                  mixSuffix x xs σ ∈ collapseAppend l σ := by
                simp [collapseAppend, h, hm]
              exact List.mem_support_of_mem hmem hp'

/-- Collapse a suffix into its mix. -/
def collapseSuffix
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (pref suff : List (Profile N V)) (hne : suff ≠ []) :
    List (Profile N V) :=
  pref ++ [Profile.mixList suff hne]

-- ----------------------------------------------------------------
-- Section 6.3: Step Function
-- ----------------------------------------------------------------

/-- One list step: if the last profile is Nash, keep the list; otherwise append
    the strict deviation and collapse on the first intersection. -/
noncomputable def stepList (l : List (Profile N V)) (hne : l ≠ []) : List (Profile N V) := by
  classical
  let σ := l.getLast hne
  by_cases h : G.IsNash σ
  · exact l
  · exact collapseAppend l (G.next σ)

theorem next_periodic (σ : Profile N V) :
    ∃ m n : ℕ, m < n ∧ ((G.next)^[m]) σ = ((G.next)^[n]) σ := by
  classical
  let f : Fin (Fintype.card (Profile N V) + 1) → Profile N V :=
    fun k => ((G.next)^[k]) σ
  have hcard : Fintype.card (Profile N V) <
      Fintype.card (Fin (Fintype.card (Profile N V) + 1)) := by
    simp
  rcases Fintype.exists_ne_map_eq_of_card_lt f hcard with ⟨i, j, hne, hEq⟩
  have hlt : i < j ∨ j < i := lt_or_gt_of_ne hne
  cases hlt with
  | inl hlt =>
      refine ⟨i.1, j.1, ?_, ?_⟩
      · exact (Fin.lt_def).1 hlt
      · simpa using hEq
  | inr hlt =>
      refine ⟨j.1, i.1, ?_, ?_⟩
      · exact (Fin.lt_def).1 hlt
      · simpa using hEq.symm

-- ----------------------------------------------------------------
-- Section 6.4: Collapse Segment Detection
-- ----------------------------------------------------------------

/-- A collapse move: σ → τ where player i deviates to a proper subface. -/
def IsCollapseStep (σ τ : Profile N V) : Prop :=
  ∃ i A, τ = σ[i ↦ A] ∧ DSimplex.IsSubface A (σ i) ∧ A ≠ σ i ∧ G.StrictDev i σ A

-- ================================================================
-- Section 7: Nash Existence - Algorithmic Approach (~150 lines)
-- ================================================================

-- ----------------------------------------------------------------
-- Section 7.1: Termination Order - Lexicographic on Lists
-- ----------------------------------------------------------------

/-- Proper subface relation on profiles (coordinate-wise proper subset). -/
def ProfileLT (σ τ : Profile N V) : Prop :=
  ProfileLE σ τ ∧ σ ≠ τ

/-- Lexicographic ordering on lists of profiles.
    L1 < L2 if at the first differing position i, L1[i] is a proper subface of L2[i]. -/
def listProfileOrder : List (Profile N V) → List (Profile N V) → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys =>
      ProfileLT x y ∨ (x = y ∧ listProfileOrder xs ys)

/-- Well-foundedness of lexicographic order on profile lists.
    This relies on Profile being finite (it's Π i, DSimplex (V i) where each DSimplex is finite). -/
theorem listProfileOrder_wf : WellFounded (listProfileOrder (N := N) (V := V)) := by
  sorry  -- Proof: Profile is finite, so ProfileLT is well-founded
         -- Lexicographic extension of well-founded relation is well-founded

instance : WellFoundedRelation (List (Profile N V)) where
  rel := listProfileOrder (N := N) (V := V)
  wf := listProfileOrder_wf

-- ----------------------------------------------------------------
-- Section 7.2: Order Increase Lemmas
-- ----------------------------------------------------------------

/-- Appending a new element (not in list) makes list strictly larger. -/
theorem listProfileOrder_append_new
    {l : List (Profile N V)} {σ : Profile N V}
    (h : σ ∉ l) :
    listProfileOrder l (l ++ [σ]) := by
  sorry  -- Proof: l is a proper prefix of l ++ [σ]

/-- If we replace a suffix with a list whose elements are all larger,
    the order increases. -/
theorem listProfileOrder_replace_suffix
    {pref suff suff' : List (Profile N V)}
    (h : suff ≠ [])
    (h' : suff' ≠ [])
    (hle : ∀ τ ∈ suff, ProfileLE τ (Profile.mixList suff' h'))
    (hproper : ∃ τ ∈ suff, ProfileLT τ (Profile.mixList suff' h')) :
    listProfileOrder (pref ++ suff) (pref ++ suff') := by
  sorry  -- Proof: At position pref.length, first element of suff' is strictly larger

/-- When stepList doesn't hit Nash and does actual work, the order increases. -/
theorem stepList_order_increases
    {l : List (Profile N V)} (hne : l ≠ [])
    (h_not_nash : ¬ G.IsNash (l.getLast hne))
    (h_changed : G.stepList l hne ≠ l) :
    listProfileOrder l (G.stepList l hne) := by
  sorry  -- Proof: Cases on whether collapseAppend actually collapses:
         -- 1. No intersection → just appends → l is proper prefix
         -- 2. Intersection but mix already in list → just appends → l is proper prefix
         -- 3. Intersection and mix new → replaces suffix with larger mix

-- ----------------------------------------------------------------
-- Section 7.3: Iteration and Termination
-- ----------------------------------------------------------------

/-- Helper: repeatedly apply stepList until Nash is reached.
    Uses well-founded recursion on listProfileOrder. -/
noncomputable def iterateToNash_aux (l : List (Profile N V)) (hne : l ≠ []) :
    List (Profile N V) := by
  sorry  -- Implementation:
         -- Use WellFounded.fix with listProfileOrder_wf
         -- If l.getLast is Nash, return l
         -- Otherwise, recurse on G.stepList l

theorem iterateToNash_aux_nonempty (l : List (Profile N V)) (hne : l ≠ []) :
    iterateToNash_aux l hne ≠ [] := by
  sorry

theorem iterateToNash_aux_nash (l : List (Profile N V)) (hne : l ≠ []) :
    G.IsNash ((iterateToNash_aux l hne).getLast (iterateToNash_aux_nonempty l hne)) := by
  sorry

-- ----------------------------------------------------------------
-- Section 7.4: Nash Equilibrium Exists (Algorithmic)
-- ----------------------------------------------------------------

/-- Nash equilibrium exists (algorithmic proof via well-founded iteration). -/
theorem nash_exists_algorithmic : ∃ σ : Profile N V, G.IsNash σ := by
  sorry  -- Proof:
         -- 1. Start from arbitrary profile σ₀
         -- 2. Apply iterateToNash_aux to get list l whose last element is Nash
         -- 3. Return l.getLast as the Nash equilibrium

/-- Constructive Nash finder: given a starting profile, find a Nash equilibrium. -/
noncomputable def findNash (σ₀ : Profile N V) : Profile N V := by
  sorry  -- Use iterateToNash_aux starting from [σ₀]

theorem findNash_is_nash (σ₀ : Profile N V) :
    G.IsNash (findNash σ₀) := by
  sorry  -- Follows from iterateToNash_aux_nash

-- ================================================================
-- Section 8: Nash Existence - Path Analysis Approach (~150 lines)
-- ================================================================

-- This section provides an alternative proof of Nash existence using
-- path analysis and the pigeonhole principle.

-- ----------------------------------------------------------------
-- Section 8.1: Infinite Paths and Pigeonhole
-- ----------------------------------------------------------------

/-- Any infinite strict deviation sequence must repeat a profile (pigeonhole). -/
theorem exists_repeat_in_infinite_path
    (f : ℕ → Profile N V)
    (h : ∀ n, G.StrictDevStep (f n) (f (n + 1))) :
    ∃ m n, m < n ∧ f m = f n := by
  sorry  -- Proof: Infinitely many naturals, finitely many profiles

/-- An infinite strict deviation path either reaches Nash or self-intersects. -/
theorem StrictDevPath_eventually_constant_or_intersects
    (f : ℕ → Profile N V)
    (h : ∀ n, G.StrictDevStep (f n) (f (n + 1))) :
    (∃ N, ∀ n ≥ N, G.IsNash (f n)) ∨
    (∃ m n, m < n ∧ Intersects (f m) (f n)) := by
  sorry  -- Proof: Either reaches Nash or by pigeonhole, repeats

-- ----------------------------------------------------------------
-- Section 8.2: Self-Intersection Creates Defenses
-- ----------------------------------------------------------------

/-- When a path self-intersects, the mix of the cycle blocks all its members. -/
theorem mix_of_cycle_blocks_members
    {l : List (Profile N V)} (hne : l ≠ [])
    (hcycle : G.StrictDevCycle l) :
    ∀ σ ∈ l, ∀ i A,
      (∃ σ' ∈ l, σ' = σ[i ↦ A] ∧ G.StrictDev i σ A) →
      ¬ G.StrictDev i (Profile.mixList l hne) (σ i) := by
  sorry  -- Proof: Use defense lemmas from Section 5

/-- When a path self-intersects, we can contract it without creating new deviations. -/
theorem contract_self_intersecting_suffix
    {l : List (Profile N V)} {σ τ : Profile N V}
    (h_path : G.StrictDevPath (l ++ [σ, τ]))
    (h_inter : ∃ ρ ∈ l, Intersects ρ τ) :
    let contracted := collapseAppend l τ
    ∀ σ' ∈ contracted, ∃ σ'' ∈ l ++ [σ, τ], ProfileLE σ' σ'' := by
  sorry  -- Proof: collapseAppend mixes intersecting suffix,
         -- all profiles in result are subfaces of originals

-- ----------------------------------------------------------------
-- Section 8.3: Path Analysis Implies Nash Existence
-- ----------------------------------------------------------------

/-- Following strict deviations from any starting point either reaches Nash
    or self-intersects, allowing contraction. The process terminates at Nash. -/
theorem nash_exists_by_path_analysis : ∃ σ : Profile N V, G.IsNash σ := by
  classical
  sorry  -- Proof sketch:
         -- 1. Start from arbitrary profile
         -- 2. If not Nash, take strict deviation
         -- 3. If path self-intersects, contract using collapseAppend
         -- 4. Either:
         --    a) Support size grows (bounded by total pure profiles), or
         --    b) List length shrinks while support constant
         -- 5. Must terminate at Nash by well-founded induction

-- ----------------------------------------------------------------
-- Section 8.4: Both Approaches Yield Nash Equilibria
-- ----------------------------------------------------------------

/-- Both proofs construct Nash equilibria (may differ, but both exist). -/
theorem nash_exists : ∃ σ : Profile N V, G.IsNash σ :=
  G.nash_exists_algorithmic

/-- The algorithmic approach is deterministic given a starting profile. -/
theorem findNash_deterministic (σ₀ : Profile N V) :
    G.IsNash (findNash σ₀) := by
  sorry  -- Follows from findNash_is_nash

end Game

end SyntheticGameTheory
