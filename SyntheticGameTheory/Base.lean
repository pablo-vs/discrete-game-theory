import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

namespace Base

-- ================================================================
-- Section 1: Sign type
-- ================================================================

inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign
  deriving DecidableEq, Repr

namespace Sign

instance : Fintype Sign :=
  ⟨{.pos, .neg, .zero}, by intro x; cases x <;> simp⟩

def flip : Sign → Sign
  | pos => neg
  | neg => pos
  | zero => zero

@[simp] theorem flip_pos : flip pos = neg := rfl
@[simp] theorem flip_neg : flip neg = pos := rfl
@[simp] theorem flip_zero : flip zero = zero := rfl
@[simp] theorem flip_flip (s : Sign) : s.flip.flip = s := by cases s <;> rfl

/-- `s.nonneg` means a ≥ b (s ∈ {pos, zero}). -/
def nonneg : Sign → Prop
  | pos => True
  | zero => True
  | neg => False

instance (s : Sign) : Decidable s.nonneg := by cases s <;> simp [nonneg] <;> infer_instance

@[simp] theorem nonneg_pos : pos.nonneg := trivial
@[simp] theorem nonneg_zero : zero.nonneg := trivial

theorem not_nonneg_neg : ¬neg.nonneg := id

theorem nonneg_flip_of_not_nonneg {s : Sign} (h : ¬s.nonneg) : s.flip.nonneg := by
  cases s <;> simp_all [nonneg, flip]

theorem not_nonneg_flip_of_nonneg_of_ne_zero {s : Sign} (h : s.nonneg) (hz : s ≠ zero) :
    ¬s.flip.nonneg := by
  cases s <;> simp_all [nonneg, flip]

/-- Multiplication of signs. Captures the sign of a product of reals. -/
def mul : Sign → Sign → Sign
  | zero, _ => zero
  | _, zero => zero
  | pos, s => s
  | neg, s => s.flip

@[simp] theorem mul_zero (s : Sign) : mul s zero = zero := by cases s <;> rfl
@[simp] theorem zero_mul (s : Sign) : mul zero s = zero := by rfl
@[simp] theorem mul_pos (s : Sign) : mul s pos = s := by cases s <;> rfl
@[simp] theorem pos_mul (s : Sign) : mul pos s = s := by cases s <;> rfl
@[simp] theorem neg_mul (s : Sign) : mul neg s = s.flip := by cases s <;> rfl

theorem flip_mul (s t : Sign) : (mul s t).flip = mul s.flip t := by
  cases s <;> cases t <;> rfl

theorem mul_nonneg {s t : Sign} (hs : s.nonneg) (ht : t.nonneg) : (mul s t).nonneg := by
  cases s <;> cases t <;> simp_all [mul, nonneg]

theorem nonneg_mul_flip_of_not_nonneg {s t : Sign} (hs : ¬s.nonneg) (ht : ¬t.nonneg) :
    (mul s t).nonneg := by
  cases s <;> cases t <;> simp_all [mul, nonneg, flip]

end Sign

-- ================================================================
-- Section 1b: Comparison sign
-- ================================================================

/-- Comparison sign of two naturals: pos if a < b, neg if a > b, zero if a = b.
    Convention: cmpSign a b = pos means "b is better" (higher index preferred). -/
def cmpSign (a b : ℕ) : Sign :=
  if a < b then Sign.pos
  else if b < a then Sign.neg
  else Sign.zero

@[simp] theorem cmpSign_self (a : ℕ) : cmpSign a a = Sign.zero := by
  simp [cmpSign]

theorem cmpSign_flip (a b : ℕ) : (cmpSign a b).flip = cmpSign b a := by
  unfold cmpSign
  split <;> (split <;> simp_all [Sign.flip] <;> omega)

theorem cmpSign_nonneg_iff {a b : ℕ} : (cmpSign a b).nonneg ↔ a ≤ b := by
  unfold cmpSign
  split
  · simp [Sign.nonneg]; omega
  · split
    · simp [Sign.nonneg]; omega
    · simp [Sign.nonneg]; omega

theorem cmpSign_trans {a b c : ℕ} (h1 : (cmpSign a b).nonneg) (h2 : (cmpSign b c).nonneg) :
    (cmpSign a c).nonneg := by
  rw [cmpSign_nonneg_iff] at *; omega

-- ================================================================
-- Section 1c: Faces (nonempty finite subsets)
-- ================================================================

@[reducible]
def Face (V : Type*) [DecidableEq V] := { S : Finset V // S.Nonempty }

namespace Face

variable {V : Type*} [DecidableEq V]

def vertex (v : V) : Face V :=
  ⟨{v}, Finset.singleton_nonempty v⟩

@[simp] theorem vertex_val {v : V} : (vertex v : Face V).1 = {v} := rfl

def full [Fintype V] [Nonempty V] : Face V :=
  ⟨Finset.univ, Finset.univ_nonempty⟩

@[simp] theorem full_val [Fintype V] [Nonempty V] : (full : Face V).1 = Finset.univ := rfl

/-- The mixture (union) of two faces. Represents mixing the strategies
    in A with those in B. -/
def mix (A B : Face V) : Face V :=
  ⟨A.1 ∪ B.1, A.2.mono Finset.subset_union_left⟩

@[simp] theorem mix_val {A B : Face V} : (mix A B).1 = A.1 ∪ B.1 := rfl

theorem mix_comm (A B : Face V) : mix A B = mix B A :=
  Subtype.ext (Finset.union_comm A.1 B.1)

theorem mix_idem (A : Face V) : mix A A = A :=
  Subtype.ext (Finset.union_self A.1)

theorem mix_assoc (A B C : Face V) : mix (mix A B) C = mix A (mix B C) :=
  Subtype.ext (Finset.union_assoc A.1 B.1 C.1)

def IsSubface (A B : Face V) : Prop := A.1 ⊆ B.1

theorem IsSubface.refl (A : Face V) : IsSubface A A := fun _ h => h

theorem IsSubface.trans {A B C : Face V} (h1 : IsSubface A B) (h2 : IsSubface B C) : IsSubface A C :=
  fun _ h => h2 (h1 h)

instance (A B : Face V) : Decidable (IsSubface A B) :=
  inferInstanceAs (Decidable (A.1 ⊆ B.1))

@[ext]
theorem ext {A B : Face V} (h : A.1 = B.1) : A = B := Subtype.ext h

instance instFintype [Fintype V] : Fintype (Face V) := by
  classical
  exact Subtype.fintype _

end Face

-- ================================================================
-- Section 2: Profile types
-- ================================================================

variable (I : Type*) [DecidableEq I] (V : I → Type*) [∀ i, DecidableEq (V i)]

abbrev PureProfile := ∀ i : I, V i
abbrev Profile := ∀ i : I, Face (V i)

scoped notation σ "[" i " ↦ " A "]" => Function.update σ i A

/-- A pure profile is consistent with a mixed profile at player i
    if every opponent's action is in their face. -/
def ConsistentAt {I : Type*} {V : I → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile I V) (i : I) (p : PureProfile I V) : Prop :=
  ∀ j, j ≠ i → p j ∈ (σ j).1

theorem ConsistentAt.update {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]
    {σ : Profile I V} {i : I} {A : Face (V i)} {p : PureProfile I V}
    (h : ConsistentAt (σ[i ↦ A]) i p) : ConsistentAt σ i p :=
  fun j hj => by have := h j hj; rwa [Function.update_of_ne hj] at this

theorem ConsistentAt.mono {I : Type*} {V : I → Type*} [∀ i, DecidableEq (V i)]
    {σ τ : Profile I V} {i : I} {p : PureProfile I V}
    (h : ConsistentAt σ i p) (hsub : ∀ j, j ≠ i → Face.IsSubface (σ j) (τ j)) :
    ConsistentAt τ i p :=
  fun j hj => hsub j hj (h j hj)

-- ================================================================
-- Section 3: SignGame structure
-- ================================================================

/-- N-player sign game. The sign function for player i takes a pure profile
    of all players and compares two actions for player i. The `sign_irrel`
    axiom ensures the sign depends only on opponents' actions. -/
structure SignGame where
  sign : (i : I) → PureProfile I V → V i → V i → Sign
  sign_refl : ∀ i p a, sign i p a a = .zero
  sign_antisym : ∀ i p a b, sign i p a b = (sign i p b a).flip
  sign_trans : ∀ i p a b c, (sign i p a b).nonneg → (sign i p b c).nonneg →
    (sign i p a c).nonneg
  sign_irrel : ∀ i p q a b, (∀ j, j ≠ i → p j = q j) → sign i p a b = sign i q a b

variable {I} {V}

namespace SignGame

variable {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]
variable (G : SignGame I V)

-- ================================================================
-- Section 4: DevFaceLE
-- ================================================================

/-- A weakly dominates B for player i against opponent profile σ:
    for every a ∈ A, every pure opponent profile consistent with σ,
    and every b ∈ B, sign i p a b ≥ 0. -/
def DevFaceLE (i : I) (σ : Profile I V) (A B : Face (V i)) : Prop :=
  ∀ a ∈ A.1, ∀ p : PureProfile I V,
    ConsistentAt σ i p → ∀ b ∈ B.1, (G.sign i p a b).nonneg

-- ================================================================
-- Section 5: Monotonicity and transitivity
-- ================================================================

namespace DevFaceLE

omit G [DecidableEq I] in
/-- Antitonicity in opponent faces: larger opponent faces make DevFaceLE harder. -/
protected theorem antitone (G : SignGame I V) {i : I} {σ τ : Profile I V}
    (h : ∀ j, j ≠ i → Face.IsSubface (σ j) (τ j))
    {A B : Face (V i)} (hle : G.DevFaceLE i τ A B) :
    G.DevFaceLE i σ A B :=
  fun a ha p hp b hb => hle a ha p (hp.mono h) b hb

omit G [DecidableEq I] in
/-- Left monotonicity: subface of A still dominates. -/
protected theorem mono_left (G : SignGame I V) {i : I} {σ : Profile I V} {A A' B : Face (V i)}
    (h : Face.IsSubface A A') (hle : G.DevFaceLE i σ A' B) :
    G.DevFaceLE i σ A B :=
  fun a ha p hp b hb => hle a (h ha) p hp b hb

omit G [DecidableEq I] in
/-- Right monotonicity: dominates superface implies dominates subface. -/
protected theorem mono_right (G : SignGame I V) {i : I} {σ : Profile I V} {A B B' : Face (V i)}
    (h : Face.IsSubface B B') (hle : G.DevFaceLE i σ A B') :
    G.DevFaceLE i σ A B :=
  fun a ha p hp b hb => hle a ha p hp b (h hb)

omit G [DecidableEq I] in
/-- Transitivity of DevFaceLE. -/
protected theorem trans (G : SignGame I V) {i : I} {σ : Profile I V} {A B C : Face (V i)}
    (hAB : G.DevFaceLE i σ A B) (hBC : G.DevFaceLE i σ B C) :
    G.DevFaceLE i σ A C := by
  intro a ha p hp c hc
  obtain ⟨b, hb⟩ := B.2
  exact G.sign_trans i p a b c (hAB a ha p hp b hb) (hBC b hb p hp c hc)

end DevFaceLE

-- ================================================================
-- Section 6: StrictDev, IsNash
-- ================================================================

/-- Player i has a strict deviation to A from profile σ. -/
def StrictDev (i : I) (σ : Profile I V) (A : Face (V i)) : Prop :=
  G.DevFaceLE i σ A (σ i) ∧ ¬G.DevFaceLE i σ (σ i) A

/-- A profile is Nash if no player has a strict deviation. -/
def IsNash (σ : Profile I V) : Prop :=
  ∀ (i : I) (A : Face (V i)), ¬G.StrictDev i σ A

-- ================================================================
-- Section 7: OutsideDominated
-- ================================================================

/-- Every included action dominates every excluded action for player i. -/
def OutsideDominated (i : I) (σ : Profile I V) : Prop :=
  ∀ v, v ∉ (σ i).1 → ∀ w, w ∈ (σ i).1 →
    G.DevFaceLE i σ (Face.vertex w) (Face.vertex v)

-- ================================================================
-- Section 8-9: OutsideDominated API
-- ================================================================

namespace OutsideDominated

omit G [DecidableEq I] in
protected theorem maximal (G : SignGame I V) (i : I)
    [∀ j, Fintype (V j)] [∀ j, Nonempty (V j)] :
    G.OutsideDominated i (fun _ => Face.full) :=
  fun v hv => absurd (Finset.mem_univ v) hv

/-- When player i restricts to A ⊆ σ i with A dominating σ i,
    OutsideDominated for player i is preserved. -/
protected theorem preserved {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDominated i σ)
    (h_sub : Face.IsSubface A (σ i))
    (h_dev : G.DevFaceLE i σ A (σ i)) :
    G.OutsideDominated i (σ[i ↦ A]) := by
  intro v hv w hw
  have hv' : v ∉ A.1 := by rwa [show (Function.update σ i A i).1 = A.1 from by
    simp [Function.update_self]] at hv
  have hw' : w ∈ A.1 := by rwa [show (Function.update σ i A i).1 = A.1 from by
    simp [Function.update_self]] at hw
  intro a ha_w p hp b hb_v
  have ha : a = w := Finset.mem_singleton.mp ha_w
  have hb : b = v := Finset.mem_singleton.mp hb_v
  subst ha; subst hb
  -- After subst: a replaces w, b replaces v; hw' : a ∈ A.1, hv' : b ∉ A.1
  have hp' : ConsistentAt σ i p := hp.update
  by_cases hb_in : b ∈ (σ i).1
  · exact h_dev a hw' p hp' b hb_in
  · exact h_inv b hb_in a (h_sub hw') a (Finset.mem_singleton_self _) p hp'
      b (Finset.mem_singleton_self _)

/-- When player i restricts, OutsideDominated for a different player j is preserved. -/
protected theorem preserved_other {i j : I} (hij : j ≠ i)
    {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDominated j σ)
    (h_sub : Face.IsSubface A (σ i)) :
    G.OutsideDominated j (σ[i ↦ A]) := by
  intro v hv w hw
  rw [Function.update_of_ne hij] at hv hw
  apply DevFaceLE.antitone G (i := j) (σ := σ[i ↦ A]) (τ := σ)
  · intro k hk
    by_cases hki : k = i
    · subst hki; exact fun x hx => h_sub (by rwa [Function.update_self] at hx)
    · intro x hx; rwa [Function.update_of_ne hki] at hx
  · exact h_inv v hv w hw

end OutsideDominated

-- ================================================================
-- Section 10: Restricting deviations
-- ================================================================

omit [DecidableEq I] in
/-- Key lemma: the backward-direction witness is in σ i. -/
private theorem outsideDom_witness_mem {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDominated i σ)
    (h_neg : ¬G.DevFaceLE i σ (σ i) A) :
    ∃ a ∈ (σ i).1, ∃ p : PureProfile I V,
      ConsistentAt σ i p ∧
      ∃ b ∈ A.1, ¬(G.sign i p a b).nonneg ∧ b ∈ (σ i).1 := by
  simp only [DevFaceLE, ConsistentAt] at h_neg; push_neg at h_neg
  obtain ⟨a, ha, p, hp, b, hb, hn⟩ := h_neg
  by_cases hb_σ : b ∈ (σ i).1
  · exact ⟨a, ha, p, hp, b, hb, hn, hb_σ⟩
  · exact absurd
      (h_inv b hb_σ a ha a (Finset.mem_singleton_self _) p hp b (Finset.mem_singleton_self _))
      hn

omit [DecidableEq I] in
/-- When OutsideDominated holds and player i has a strict deviation to A,
    there exists a restricting strict deviation A' ⊆ σ i with A' ≠ σ i. -/
theorem exists_restrictingStrictDev {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDominated i σ)
    (h_dev : G.StrictDev i σ A) :
    ∃ A' : Face (V i),
      G.StrictDev i σ A' ∧ Face.IsSubface A' (σ i) ∧ A' ≠ σ i := by
  obtain ⟨h_fwd, h_bwd⟩ := h_dev
  obtain ⟨a, ha_σ, p, hp, b, hb_A, hn, hb_σ⟩ := outsideDom_witness_mem G h_inv h_bwd
  let A' : Face (V i) := ⟨A.1 ∩ (σ i).1, ⟨b, Finset.mem_inter.mpr ⟨hb_A, hb_σ⟩⟩⟩
  refine ⟨A', ⟨?_, ?_⟩, Finset.inter_subset_right, ?_⟩
  · exact DevFaceLE.mono_left G Finset.inter_subset_left h_fwd
  · intro h_contra
    exact absurd (h_contra a ha_σ p hp b (Finset.mem_inter.mpr ⟨hb_A, hb_σ⟩)) hn
  · intro heq
    have h_σ_sub_A : Face.IsSubface (σ i) A := by
      intro x hx; exact (Finset.mem_inter.mp (heq ▸ hx)).1
    apply h_bwd
    intro x hx p' hp' y hy
    by_cases hy_σ : y ∈ (σ i).1
    · exact (DevFaceLE.mono_left G h_σ_sub_A h_fwd) x hx p' hp' y hy_σ
    · exact h_inv y hy_σ x hx x (Finset.mem_singleton_self _) p' hp'
        y (Finset.mem_singleton_self _)

-- ================================================================
-- Section 11: Profile size and descent
-- ================================================================

omit G in
def profileSize [Fintype I] (σ : Profile I V) : ℕ :=
  Finset.univ.sum (fun i => (σ i).1.card)

omit G in
theorem profileSize_decreases [Fintype I] {i : I} {σ : Profile I V} {A : Face (V i)}
    (hsub : Face.IsSubface A (σ i)) (hne : A ≠ σ i) :
    profileSize (σ[i ↦ A]) < profileSize σ := by
  unfold profileSize
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hji : j = i
    · subst hji; simp only [Function.update_self]; exact Finset.card_le_card hsub
    · rw [Function.update_of_ne hji]
  · exact ⟨i, Finset.mem_univ i, by
      simp only [Function.update_self]
      exact Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (Face.ext h)⟩)⟩

-- ================================================================
-- Section 12: Nash existence
-- ================================================================

/-- Nash existence from any profile satisfying OutsideDominated.
    Used directly for finite games (starting from full profile) and
    for restriction to a compact core (starting from the core profile). -/
theorem nash_exists_of_OD [Fintype I]
    (σ : Profile I V)
    (h_od : ∀ i, G.OutsideDominated i σ) :
    ∃ τ, G.IsNash τ := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h⟩
  · simp only [IsNash, not_forall, not_not] at h
    obtain ⟨i₀, A, hA⟩ := h
    obtain ⟨A', hdev, hsub, hne⟩ := exists_restrictingStrictDev G (h_od i₀) hA
    have hdec := profileSize_decreases hsub hne
    exact nash_exists_of_OD (σ[i₀ ↦ A']) (fun j => by
      by_cases hij : j = i₀
      · subst hij; exact OutsideDominated.preserved G (h_od j) hsub hdev.1
      · exact OutsideDominated.preserved_other G hij (h_od j) hsub)
  termination_by profileSize σ

theorem nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.IsNash σ :=
  nash_exists_of_OD G (fun _ => Face.full) (fun i => OutsideDominated.maximal G i)

-- ================================================================
-- Section 13: Nash existence with subface and OD tracking
-- ================================================================

theorem nash_exists_sub_OD [Fintype I]
    (σ : Profile I V)
    (h_od : ∀ i, G.OutsideDominated i σ) :
    ∃ τ, G.IsNash τ ∧ (∀ i, Face.IsSubface (τ i) (σ i)) ∧
      (∀ i, G.OutsideDominated i τ) := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h, fun _ x hx => hx, h_od⟩
  · simp only [IsNash, not_forall, not_not] at h
    obtain ⟨i₀, A, hA⟩ := h
    obtain ⟨A', hdev, hsub, hne⟩ := exists_restrictingStrictDev G (h_od i₀) hA
    have hdec := profileSize_decreases hsub hne
    have h_od' : ∀ j, G.OutsideDominated j (σ[i₀ ↦ A']) := fun j => by
      by_cases hij : j = i₀
      · subst hij; exact OutsideDominated.preserved G (h_od j) hsub hdev.1
      · exact OutsideDominated.preserved_other G hij (h_od j) hsub
    obtain ⟨τ, hτN, hτ_sub, hτ_od⟩ := nash_exists_sub_OD (σ[i₀ ↦ A']) h_od'
    refine ⟨τ, hτN, fun j => ?_, hτ_od⟩
    by_cases hji : j = i₀
    · subst hji
      intro x hx
      have hx' := hτ_sub j hx
      rw [Function.update_self] at hx'
      exact hsub hx'
    · intro x hx
      have := hτ_sub j hx
      rwa [Function.update_of_ne hji] at this
  termination_by profileSize σ

-- ================================================================
-- Section 14: Building SignGame from payoffs
-- ================================================================

/-- Construct a SignGame from payoff functions. -/
def ofPayoffs [Fintype I]
    (u : (i : I) → (∀ j, V j) → Int) : SignGame I V where
  sign i p a b :=
    let pa := Function.update p i a
    let pb := Function.update p i b
    if u i pa > u i pb then .pos
    else if u i pa = u i pb then .zero
    else .neg
  sign_refl i p a := by simp
  sign_antisym i p a b := by
    simp only [Sign.flip]
    split_ifs <;> first | rfl | omega
  sign_trans i p a b c := by
    simp only [Sign.nonneg]
    split_ifs <;> simp_all <;> omega
  sign_irrel i p q a b h := by
    have hpa : Function.update p i a = Function.update q i a := by
      ext j; by_cases hji : j = i
      · subst hji; simp [Function.update_self]
      · simp [Function.update_of_ne hji, h j hji]
    have hpb : Function.update p i b = Function.update q i b := by
      ext j; by_cases hji : j = i
      · subst hji; simp [Function.update_self]
      · simp [Function.update_of_ne hji, h j hji]
    simp only [hpa, hpb]

-- ================================================================
-- Section 15: Pure Nash and examples
-- ================================================================

/-- Pure Nash: no player can improve by switching action. -/
def IsPureNash (p : PureProfile I V) : Prop :=
  ∀ (i : I) (v : V i), (G.sign i p (p i) v).nonneg

end SignGame

end Base
