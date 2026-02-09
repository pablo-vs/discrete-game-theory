import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Discrete Simplex
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
-- Section 2: Profiles
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

-- ================================================================
-- Section 3: Games
-- ================================================================

/-- A game: N players, V i actions for player i, payoffs on pure profiles. -/
structure Game (N : Type*) [DecidableEq N]
    (V : N → Type*) [∀ i, DecidableEq (V i)] where
  /-- Player `i`'s preference preorder on pure profiles. -/
  pref : N → PureProfile N V → PureProfile N V → Prop
  /-- Each player's preference is a preorder on pure profiles. -/
  pref_preorder : ∀ i : N, IsPreorder (PureProfile N V) (pref i)
  /-- Each player's preference is total on pure profiles. -/
  pref_total : ∀ i : N, Std.Total (pref i)
  /-- Preference is decidable for each player. -/
  pref_decidable : ∀ i : N, DecidableRel (pref i)

-- ================================================================
-- Section 4: Face Ordering and Deviations
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

/-- A Best Response for player `i` against `σ` is a face `A` such that `i` has no
    strict deviation from `σ[i ↦ A]`. -/
def IsBestResponse (i : N) (σ : Profile N V) (A : DSimplex (V i)) : Prop :=
  ∀ B, ¬ G.StrictDev i (σ[i ↦ A]) B

/-- A Strict Best Response deviation. -/
def StrictBestResponse (i : N) (σ : Profile N V) (A : DSimplex (V i)) : Prop :=
  G.StrictDev i σ A ∧ G.IsBestResponse i σ A

/-- Every vertex outside σ i is weakly dominated by every vertex inside σ i. -/
def OutsideDominated (i : N) (σ : Profile N V) : Prop :=
  ∀ v, v ∉ (σ i).1 → ∀ w, w ∈ (σ i).1 →
    G.DevFaceLE i σ (DSimplex.vertex v) (DSimplex.vertex w)

/-- A restricting strict deviation: strict deviation to a proper subface. -/
def RestrictingStrictDev (i : N) (σ : Profile N V) (A : DSimplex (V i)) : Prop :=
  G.StrictDev i σ A ∧ DSimplex.IsSubface A (σ i) ∧ A ≠ σ i

-- ----------------------------------------------------------------
-- Section 4.2: DevFaceLE Properties
-- ----------------------------------------------------------------

omit [Fintype N] [∀ i, Fintype (V i)] in
/-- `DevFaceLE` is transitive. -/
theorem DevFaceLE_trans (i : N) (σ : Profile N V) (A B C : DSimplex (V i)) :
    G.DevFaceLE i σ A B → G.DevFaceLE i σ B C → G.DevFaceLE i σ A C := by
  intro hAB hBC p hp r hr
  classical
  let b := Classical.choose B.2
  have hb : b ∈ B.1 := Classical.choose_spec B.2
  let q : PureProfile N V := fun j => if h : j = i then h ▸ b else p j
  have hq : Consistent (σ[i ↦ B]) q := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [q]
      exact hb
    · simp [q, hji]
      show p j ∈ (σ j).1
      have : (σ[i ↦ A] j) = (σ j) := by simp [Function.update, dif_neg hji]
      rw [← this]
      exact hp j
  have hpq : G.pref i p q := hAB p hp q hq
  have hqr : G.pref i q r := hBC q hq r hr
  have : IsTrans (PureProfile N V) (G.pref i) := G.pref_preorder i |>.toIsTrans
  exact this.trans p q r hpq hqr

omit [Fintype N] [∀ i, Fintype (V i)] in
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

omit [Fintype N] [∀ i, Fintype (V i)] in
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

omit [Fintype N] [∀ i, Fintype (V i)] in
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

omit [Fintype N] [∀ i, Fintype (V i)] in
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

-- ----------------------------------------------------------------
-- Section 4.3: Better Relation and Best Response Existence
-- ----------------------------------------------------------------

/-- `Better` relation: A is strictly better than B for player i against σ_{-i}. -/
def Better (i : N) (σ : Profile N V) (A B : DSimplex (V i)) : Prop :=
  G.StrictDev i (σ[i ↦ B]) A

omit [Fintype N] [∀ i, Fintype (V i)] in
theorem Better_irref (i : N) (σ : Profile N V) (A : DSimplex (V i)) :
    ¬ G.Better i σ A A := by
  intro h
  unfold Better StrictDev at h
  rcases h with ⟨h1, h2⟩
  rw [Function.update_self] at h1 h2
  exact h2 h1

omit [Fintype N] [∀ i, Fintype (V i)] in
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

omit [Fintype N] in
theorem exists_best_response (i : N) (σ : Profile N V) :
    ∃ A : DSimplex (V i), G.IsBestResponse i σ A := by
  classical
  have h_exists : ∃ m, ∀ x, ¬ G.Better i σ x m := by
    -- Better is a strict partial order on a finite type, hence well-founded
    haveI : IsTrans _ (G.Better i σ) := ⟨fun a b c => G.Better_trans i σ⟩
    haveI : Std.Irrefl (G.Better i σ) := ⟨fun a => G.Better_irref i σ a⟩
    have h_wf : WellFounded (G.Better i σ) := Finite.wellFounded_of_trans_of_irrefl _
    obtain ⟨m, -, hm⟩ := h_wf.has_min Set.univ ⟨σ i, trivial⟩
    exact ⟨m, fun x => hm x trivial⟩
  obtain ⟨m, hm⟩ := h_exists
  refine ⟨m, ?_⟩
  intro B
  exact hm B

omit [Fintype N] [∀ i, Fintype (V i)] in
/-- Existence of a strict deviation when not Nash (classical). -/
theorem exists_strictDev_of_not_nash
    {σ : Profile N V} (h : ¬ G.IsNash σ) :
    ∃ i : N, ∃ A : DSimplex (V i), G.StrictDev i σ A := by
  classical
  simpa [IsNash] using h

-- ----------------------------------------------------------------
-- Section 4.4: Invariant Results
-- ----------------------------------------------------------------

omit [Fintype N] in
/-- The maximal profile trivially satisfies OutsideDominated. -/
theorem OutsideDominated_maximal [∀ i, Nonempty (V i)] (i : N) :
    G.OutsideDominated i (fun _ => ⟨Finset.univ, Finset.univ_nonempty⟩) := by
  intro v hv
  exact absurd (Finset.mem_univ v) hv

omit [Fintype N] [∀ i, Fintype (V i)] in
/-- OutsideDominated is preserved under restricting steps. -/
theorem OutsideDominated_preserved
    {σ : Profile N V} {i : N} {A : DSimplex (V i)}
    (h_inv : ∀ j, G.OutsideDominated j σ)
    (h_sub : DSimplex.IsSubface A (σ i))
    (h_dev : G.DevFaceLE i σ (σ i) A) :
    ∀ j, G.OutsideDominated j (σ[i ↦ A]) := by
  -- ProfileLE (σ[i ↦ A]) σ since A ⊆ σ i
  have hle : ProfileLE (σ[i ↦ A]) σ := by
    intro k; by_cases hki : k = i
    · subst hki; simpa using h_sub
    · simp [hki, DSimplex.IsSubface]
  intro j v hv w hw
  by_cases hji : j = i
  · subst hji
    simp at hv hw
    by_cases hv_in : v ∈ (σ j).1
    · -- v was in σ j but not in A: newly excluded
      have hv_sub : DSimplex.IsSubface (DSimplex.vertex v) (σ j) := by
        simp [DSimplex.IsSubface]; exact hv_in
      have hw_sub : DSimplex.IsSubface (DSimplex.vertex w) A := by
        simp [DSimplex.IsSubface]; exact hw
      have h1 : G.DevFaceLE j σ (DSimplex.vertex v) A :=
        G.DevFaceLE_left_mono hv_sub h_dev
      have h2 : G.DevFaceLE j σ (DSimplex.vertex v) (DSimplex.vertex w) :=
        G.DevFaceLE_right_mono hw_sub h1
      exact G.DevFaceLE_antitone hle j _ _ h2
    · -- v was already outside σ j
      have hw_in : w ∈ (σ j).1 := h_sub hw
      have h1 : G.DevFaceLE j σ (DSimplex.vertex v) (DSimplex.vertex w) :=
        h_inv j v hv_in w hw_in
      exact G.DevFaceLE_antitone hle j _ _ h1
  · -- j ≠ i: face unchanged
    have heq_j : (σ[i ↦ A]) j = σ j := by simp [Function.update, dif_neg hji]
    rw [heq_j] at hv hw
    have h1 : G.DevFaceLE j σ (DSimplex.vertex v) (DSimplex.vertex w) :=
      h_inv j v hv w hw
    exact G.DevFaceLE_antitone hle j _ _ h1

omit [Fintype N] [∀ i, Fintype (V i)] in
/-- When OutsideDominated holds and ¬DevFaceLE i σ A (σ i), the witness
    pure profile has p i ∈ (σ i).1. -/
private theorem outsideDominated_neg_witness_mem
    {i : N} {σ : Profile N V} {A : DSimplex (V i)}
    (h_inv : G.OutsideDominated i σ)
    (h_neg : ¬G.DevFaceLE i σ A (σ i)) :
    ∃ p q, Consistent (σ[i ↦ A]) p ∧ Consistent (σ[i ↦ σ i]) q ∧
      ¬G.pref i p q ∧ p i ∈ A.1 ∧ p i ∈ (σ i).1 := by
  classical
  -- Unfold the negation: ∃ p q, ...
  rw [DevFaceLE] at h_neg
  push_neg at h_neg
  obtain ⟨p, hp, q, hq, h_not_pref⟩ := h_neg
  -- p i ∈ A.1 by consistency
  have hp_i : p i ∈ A.1 := by
    have := hp i; simp at this; exact this
  -- q i ∈ (σ i).1 by consistency
  have hq_i : q i ∈ (σ i).1 := by
    have := hq i; simp at this; exact this
  -- Must show p i ∈ (σ i).1
  by_cases h_mem : p i ∈ (σ i).1
  · exact ⟨p, q, hp, hq, h_not_pref, hp_i, h_mem⟩
  · -- If p i ∉ (σ i).1, OutsideDominated gives pref i p q, contradiction
    exfalso
    have : G.DevFaceLE i σ (DSimplex.vertex (p i)) (DSimplex.vertex (q i)) :=
      h_inv (p i) h_mem (q i) hq_i
    -- Specialize to p and q
    have h_pref : G.pref i p q := by
      apply this
      · intro k; by_cases hki : k = i
        · subst hki; simp; exact Finset.mem_singleton_self _
        · simp [hki]; have := hp k; simp [hki] at this; exact this
      · intro k; by_cases hki : k = i
        · subst hki; simp; exact Finset.mem_singleton_self _
        · simp [hki]; have := hq k; simp [hki] at this; exact this
    exact h_not_pref h_pref

omit [Fintype N] [∀ i, Fintype (V i)] in
/-- When not Nash and OutsideDominated holds, there exists a restricting strict deviation. -/
theorem exists_restrictingStrictDev_of_not_nash_with_outsideDom
    {σ : Profile N V}
    (h_inv : ∀ i, G.OutsideDominated i σ)
    (h : ¬G.IsNash σ) :
    ∃ i, ∃ A, G.RestrictingStrictDev i σ A := by
  classical
  obtain ⟨i, A, hdev⟩ := G.exists_strictDev_of_not_nash h
  -- Get witness from the backward direction ¬DevFaceLE i σ A (σ i)
  obtain ⟨p, q, hp, hq, h_not_pref, hp_i_A, hp_i_σ⟩ :=
    G.outsideDominated_neg_witness_mem (h_inv i) hdev.2
  -- Define A' = A ∩ σ i (nonempty since p i is in both)
  have h_ne : (A.1 ∩ (σ i).1).Nonempty := ⟨p i, Finset.mem_inter.mpr ⟨hp_i_A, hp_i_σ⟩⟩
  let A' : DSimplex (V i) := ⟨A.1 ∩ (σ i).1, h_ne⟩
  -- A' ⊆ A
  have hA'_sub_A : DSimplex.IsSubface A' A := by
    show A.1 ∩ (σ i).1 ⊆ A.1
    exact Finset.inter_subset_left
  -- A' ⊆ σ i
  have hA'_sub_σ : DSimplex.IsSubface A' (σ i) := by
    show A.1 ∩ (σ i).1 ⊆ (σ i).1
    exact Finset.inter_subset_right
  -- StrictDev i σ A' — forward: σ i ≤ A' via right_mono from σ i ≤ A
  have h_fwd : G.DevFaceLE i σ (σ i) A' :=
    G.DevFaceLE_right_mono hA'_sub_A hdev.1
  -- StrictDev i σ A' — backward: ¬(A' ≤ σ i), via the witness p, q
  have h_bwd : ¬G.DevFaceLE i σ A' (σ i) := by
    intro h_contra
    have hp' : Consistent (σ[i ↦ A']) p := by
      intro k; by_cases hki : k = i
      · subst hki; simp; exact Finset.mem_inter.mpr ⟨hp_i_A, hp_i_σ⟩
      · simp [hki]; have := hp k; simp [hki] at this; exact this
    exact h_not_pref (h_contra p hp' q hq)
  -- A' ≠ σ i: else h_fwd and h_bwd contradict
  have hA'_ne : A' ≠ σ i := by
    intro heq
    rw [heq] at h_fwd h_bwd
    exact h_bwd h_fwd
  exact ⟨i, A', ⟨h_fwd, h_bwd⟩, hA'_sub_σ, hA'_ne⟩

-- ================================================================
-- Section 5: Profile Size and Descent
-- ================================================================

/-- Total number of vertices across all players' faces. -/
def profileSize (σ : Profile N V) : ℕ :=
  Finset.univ.sum (fun i => (σ i).1.card)

omit [∀ i, Fintype (V i)] in
/-- Profile size strictly decreases when replacing a face with a proper subface. -/
theorem profileSize_decreases_of_restricting
    {i : N} {σ : Profile N V} {A : DSimplex (V i)}
    (hsub : DSimplex.IsSubface A (σ i)) (hne : A ≠ σ i) :
    profileSize (σ[i ↦ A]) < profileSize σ := by
  unfold profileSize
  have hcard : A.1.card < (σ i).1.card := by
    have : A.1 ⊂ (σ i).1 := by
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (DSimplex.ext h)⟩
    exact Finset.card_lt_card this
  conv_lhs => rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
  conv_rhs => rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
  have h_at_i : ((σ[i ↦ A]) i).1.card = A.1.card := by
    show (Function.update σ i A i).1.card = A.1.card
    unfold Function.update
    split_ifs
    · rfl
    · contradiction
  have h_elsewhere : ∀ j ∈ Finset.univ.erase i, ((σ[i ↦ A]) j).1.card = (σ j).1.card := by
    intro j hj
    have hjne : j ≠ i := Finset.mem_erase.mp hj |>.1
    show (Function.update σ i A j).1.card = (σ j).1.card
    unfold Function.update
    split_ifs with h
    · subst h; contradiction
    · rfl
  rw [h_at_i]
  rw [Finset.sum_congr rfl h_elsewhere]
  omega

-- ================================================================
-- Section 6: Nash Existence via Well-Founded Descent
-- ================================================================

/-- Maximal profile with all vertices. -/
noncomputable def maximalProfile [∀ i, Nonempty (V i)] : Profile N V :=
  fun _ => ⟨Finset.univ, Finset.univ_nonempty⟩

omit [∀ i, Fintype (V i)] in
/-- Nash existence by well-founded descent with threaded invariant. -/
private theorem nash_exists_aux (σ : Profile N V)
    (h_inv : ∀ i, G.OutsideDominated i σ) :
    ∃ τ : Profile N V, G.IsNash τ := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h⟩
  · obtain ⟨i, A, hdev, hsub, hne⟩ :=
      G.exists_restrictingStrictDev_of_not_nash_with_outsideDom h_inv h
    have h_inv' := G.OutsideDominated_preserved h_inv hsub hdev.1
    have : profileSize (σ[i ↦ A]) < profileSize σ :=
      profileSize_decreases_of_restricting hsub hne
    exact nash_exists_aux (σ[i ↦ A]) h_inv'
termination_by profileSize σ

/-- Nash equilibrium existence - main theorem. -/
theorem nash_exists [∀ i, Nonempty (V i)] : ∃ σ : Profile N V, G.IsNash σ :=
  G.nash_exists_aux maximalProfile (fun i => G.OutsideDominated_maximal i)

end Game

end SyntheticGameTheory
