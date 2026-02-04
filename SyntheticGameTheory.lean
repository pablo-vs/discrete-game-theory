import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

namespace SyntheticGameTheory

-- ================================================================
-- Part 1: Discrete simplex
-- ================================================================

/-- A discrete simplex on vertex set V. Elements are nonempty subsets
    of V, each representing the interior of the face spanned by those
    vertices. -/
@[reducible]
def DSimplex (V : Type*) [DecidableEq V] :=
  { S : Finset V // S.Nonempty }

namespace DSimplex

variable {V : Type*} [DecidableEq V]

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
-- Part 2: Profiles and games
-- ================================================================

/-- A pure profile: each player picks a vertex (pure action). -/
abbrev PureProfile (N : Type*) (V : N → Type*) := ∀ i : N, V i

/-- A profile: each player picks a face of their simplex. -/
abbrev Profile (N : Type*) (V : N → Type*) [∀ i, DecidableEq (V i)] :=
  ∀ i : N, DSimplex (V i)

/-- Notation for profile deviation: σ[i ↦ s] means "profile σ with player i
    updated to play s". -/
notation:max σ:max "[" i " ↦ " s "]" => Function.update σ i s

/-- A pure profile `p` is consistent with a mixed profile `σ` if each action is
    in the support of the corresponding face. -/
def Consistent
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile N V) (p : PureProfile N V) : Prop :=
  ∀ i, p i ∈ DSimplex.support (σ i)

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

def Profile.mixList
    {N : Type*} {V : N → Type*} [∀ i, DecidableEq (V i)]
    (l : List (Profile N V)) (hne : l ≠ []) : Profile N V :=
  match l with
  | [] => (hne rfl).elim
  | x :: xs => xs.foldl Profile.mix x

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

namespace Game

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]

variable (G : Game N V)

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

/-- A defense against dominance of `B` by `A`. -/
def Defends (i : N) (σ : Profile N V) (A B : DSimplex (V i)) : Prop :=
  ¬ G.DevFaceLE i σ A B

/-- `DevFaceLE` is antitone in the profile argument: enlarging opponents makes the
    relation harder to satisfy. -/
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

/-- `DevFaceLE` is monotone in the left face (shrinking the left face preserves it). -/
theorem DevFaceLE_left_mono
    {i : N} {σ : Profile N V} {A A' B : DSimplex (V i)}
    (h : DSimplex.IsSubface A A') :
    G.DevFaceLE i σ A' B → G.DevFaceLE i σ A B := by
  intro hle p hp q hq
  have hp' : Consistent (σ[i ↦ A']) p := by
    apply Consistent_mono (ProfileLE_update_left σ i h)
    exact hp
  exact hle p hp' q hq

/-- `DevFaceLE` is monotone in the right face (shrinking the right face preserves it). -/
theorem DevFaceLE_right_mono
    {i : N} {σ : Profile N V} {A B B' : DSimplex (V i)}
    (h : DSimplex.IsSubface B B') :
    G.DevFaceLE i σ A B' → G.DevFaceLE i σ A B := by
  intro hle p hp q hq
  have hq' : Consistent (σ[i ↦ B']) q := by
    apply Consistent_mono (ProfileLE_update_left σ i h)
    exact hq
  exact hle p hp q hq'

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

theorem StrictDev_defends
    {i : N} {σ : Profile N V} {A : DSimplex (V i)} :
    G.StrictDev i σ A → G.Defends i σ A (σ i) := by
  intro h
  exact h.2

end Game

end SyntheticGameTheory
