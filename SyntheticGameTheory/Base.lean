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

def full [Fintype V] [Nonempty V] : Face V :=
  ⟨Finset.univ, Finset.univ_nonempty⟩

/-- The mixture (union) of two faces. Represents mixing the strategies
    in A with those in B. -/
def mix (A B : Face V) : Face V :=
  ⟨A.1 ∪ B.1, A.2.mono Finset.subset_union_left⟩

theorem mix_comm (A B : Face V) : mix A B = mix B A :=
  Subtype.ext (Finset.union_comm A.1 B.1)

theorem mix_idem (A : Face V) : mix A A = A :=
  Subtype.ext (Finset.union_self A.1)

theorem mix_assoc (A B C : Face V) : mix (mix A B) C = mix A (mix B C) :=
  Subtype.ext (Finset.union_assoc A.1 B.1 C.1)

def IsSubface (A B : Face V) : Prop := A.1 ⊆ B.1

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
    (∀ j, j ≠ i → p j ∈ (σ j).1) → ∀ b ∈ B.1, (G.sign i p a b).nonneg

-- ================================================================
-- Section 5: Monotonicity and transitivity
-- ================================================================

set_option linter.unusedSectionVars false in
/-- Antitonicity in opponent faces: larger opponent faces make DevFaceLE harder. -/
theorem DevFaceLE_antitone {i : I} {σ τ : Profile I V}
    (h : ∀ j, j ≠ i → Face.IsSubface (σ j) (τ j))
    {A B : Face (V i)} (hle : G.DevFaceLE i τ A B) :
    G.DevFaceLE i σ A B :=
  fun a ha p hp b hb => hle a ha p (fun j hj => h j hj (hp j hj)) b hb

set_option linter.unusedSectionVars false in
/-- Left monotonicity: subface of A still dominates. -/
theorem DevFaceLE_left_mono {i : I} {σ : Profile I V} {A A' B : Face (V i)}
    (h : Face.IsSubface A A') (hle : G.DevFaceLE i σ A' B) :
    G.DevFaceLE i σ A B :=
  fun a ha p hp b hb => hle a (h ha) p hp b hb

set_option linter.unusedSectionVars false in
/-- Right monotonicity: dominates superface implies dominates subface. -/
theorem DevFaceLE_right_mono {i : I} {σ : Profile I V} {A B B' : Face (V i)}
    (h : Face.IsSubface B B') (hle : G.DevFaceLE i σ A B') :
    G.DevFaceLE i σ A B :=
  fun a ha p hp b hb => hle a ha p hp b (h hb)

set_option linter.unusedSectionVars false in
/-- Transitivity of DevFaceLE. -/
theorem DevFaceLE_trans {i : I} {σ : Profile I V} {A B C : Face (V i)}
    (hAB : G.DevFaceLE i σ A B) (hBC : G.DevFaceLE i σ B C) :
    G.DevFaceLE i σ A C := by
  intro a ha p hp c hc
  obtain ⟨b, hb⟩ := B.2
  exact G.sign_trans i p a b c (hAB a ha p hp b hb) (hBC b hb p hp c hc)

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
-- Section 8: OutsideDominated base case
-- ================================================================

theorem OutsideDominated_maximal (i : I)
    [∀ j, Fintype (V j)] [∀ j, Nonempty (V j)] :
    G.OutsideDominated i (fun _ => Face.full) :=
  fun v hv => absurd (Finset.mem_univ v) hv

-- ================================================================
-- Section 9: OutsideDominated preservation
-- ================================================================

/-- When player i restricts to A ⊆ σ i with A dominating σ i,
    OutsideDominated for player i is preserved. -/
theorem OutsideDominated_preserved {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDominated i σ)
    (h_sub : Face.IsSubface A (σ i))
    (h_dev : G.DevFaceLE i σ A (σ i)) :
    G.OutsideDominated i (Function.update σ i A) := by
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
  have hp' : ∀ j, j ≠ i → p j ∈ (σ j).1 := fun j hj => by
    have := hp j hj; rwa [Function.update_of_ne hj] at this
  by_cases hb_in : b ∈ (σ i).1
  · exact h_dev a hw' p hp' b hb_in
  · exact h_inv b hb_in a (h_sub hw') a (Finset.mem_singleton_self _) p hp'
      b (Finset.mem_singleton_self _)

/-- When player i restricts, OutsideDominated for a different player j is preserved. -/
theorem OutsideDominated_preserved_other {i j : I} (hij : j ≠ i)
    {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDominated j σ)
    (h_sub : Face.IsSubface A (σ i)) :
    G.OutsideDominated j (Function.update σ i A) := by
  intro v hv w hw
  rw [Function.update_of_ne hij] at hv hw
  apply DevFaceLE_antitone G (i := j) (σ := Function.update σ i A) (τ := σ)
  · intro k hk
    by_cases hki : k = i
    · subst hki; exact fun x hx => h_sub (by rwa [Function.update_self] at hx)
    · intro x hx; rwa [Function.update_of_ne hki] at hx
  · exact h_inv v hv w hw

-- ================================================================
-- Section 10: Restricting deviations
-- ================================================================

set_option linter.unusedSectionVars false in
/-- Key lemma: the backward-direction witness is in σ i. -/
private theorem outsideDom_witness_mem {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDominated i σ)
    (h_neg : ¬G.DevFaceLE i σ (σ i) A) :
    ∃ a ∈ (σ i).1, ∃ p : PureProfile I V,
      (∀ j, j ≠ i → p j ∈ (σ j).1) ∧
      ∃ b ∈ A.1, ¬(G.sign i p a b).nonneg ∧ b ∈ (σ i).1 := by
  simp only [DevFaceLE] at h_neg; push_neg at h_neg
  obtain ⟨a, ha, p, hp, b, hb, hn⟩ := h_neg
  by_cases hb_σ : b ∈ (σ i).1
  · exact ⟨a, ha, p, hp, b, hb, hn, hb_σ⟩
  · exact absurd
      (h_inv b hb_σ a ha a (Finset.mem_singleton_self _) p hp b (Finset.mem_singleton_self _))
      hn

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
  · exact DevFaceLE_left_mono G Finset.inter_subset_left h_fwd
  · intro h_contra
    exact absurd (h_contra a ha_σ p hp b (Finset.mem_inter.mpr ⟨hb_A, hb_σ⟩)) hn
  · intro heq
    have h_σ_sub_A : Face.IsSubface (σ i) A := by
      intro x hx; exact (Finset.mem_inter.mp (heq ▸ hx)).1
    apply h_bwd
    intro x hx p' hp' y hy
    by_cases hy_σ : y ∈ (σ i).1
    · exact (DevFaceLE_left_mono G h_σ_sub_A h_fwd) x hx p' hp' y hy_σ
    · exact h_inv y hy_σ x hx x (Finset.mem_singleton_self _) p' hp'
        y (Finset.mem_singleton_self _)

-- ================================================================
-- Section 11: Profile size and descent
-- ================================================================

set_option linter.unusedSectionVars false in
def profileSize [Fintype I] (σ : Profile I V) : ℕ :=
  Finset.univ.sum (fun i => (σ i).1.card)

set_option linter.unusedSectionVars false in
theorem profileSize_decreases [Fintype I] {i : I} {σ : Profile I V} {A : Face (V i)}
    (hsub : Face.IsSubface A (σ i)) (hne : A ≠ σ i) :
    profileSize (Function.update σ i A) < profileSize σ := by
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

private theorem nash_exists_aux [Fintype I]
    (σ : Profile I V)
    (h_od : ∀ i, G.OutsideDominated i σ) :
    ∃ τ, G.IsNash τ := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h⟩
  · simp only [IsNash, not_forall, not_not] at h
    obtain ⟨i₀, A, hA⟩ := h
    obtain ⟨A', hdev, hsub, hne⟩ := exists_restrictingStrictDev G (h_od i₀) hA
    have hdec := profileSize_decreases hsub hne
    exact nash_exists_aux (Function.update σ i₀ A') (fun j => by
      by_cases hij : j = i₀
      · subst hij; exact OutsideDominated_preserved G (h_od j) hsub hdev.1
      · exact OutsideDominated_preserved_other G hij (h_od j) hsub)
  termination_by profileSize σ

theorem nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.IsNash σ :=
  nash_exists_aux G (fun _ => Face.full) (fun i => OutsideDominated_maximal G i)

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
    have h_od' : ∀ j, G.OutsideDominated j (Function.update σ i₀ A') := fun j => by
      by_cases hij : j = i₀
      · subst hij; exact OutsideDominated_preserved G (h_od j) hsub hdev.1
      · exact OutsideDominated_preserved_other G hij (h_od j) hsub
    obtain ⟨τ, hτN, hτ_sub, hτ_od⟩ := nash_exists_sub_OD (Function.update σ i₀ A') h_od'
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

-- ================================================================
-- 2×2 game examples (I = Fin 2, V = fun _ => Bool)
-- ================================================================

/-- Helper: compute sign from two Ints -/
def intSign (a b : Int) : Sign :=
  if a > b then .pos
  else if a = b then .zero
  else .neg

theorem intSign_refl (a : Int) : intSign a a = .zero := by
  simp [intSign]

theorem intSign_antisym (a b : Int) : intSign a b = (intSign b a).flip := by
  simp only [intSign, Sign.flip]; split_ifs <;> first | rfl | omega

theorem intSign_trans (a b c : Int) :
    (intSign a b).nonneg → (intSign b c).nonneg → (intSign a c).nonneg := by
  simp only [intSign, Sign.nonneg]; split_ifs <;> simp_all <;> omega

/-- Construct a 2-player Bool game from payoff matrices.
    Uses explicit sign computation to enable `decide`. -/
def game2x2 (u_TT u_TF u_FT u_FF : Int) (v_TT v_TF v_FT v_FF : Int) :
    SignGame (Fin 2) (fun _ : Fin 2 => Bool) where
  sign i p a b :=
    let opp := p (1 - i)
    if (i : ℕ) = 0 then
      intSign
        (if a then (if opp then u_TT else u_TF) else (if opp then u_FT else u_FF))
        (if b then (if opp then u_TT else u_TF) else (if opp then u_FT else u_FF))
    else
      intSign
        (if opp then (if a then v_TT else v_TF) else (if a then v_FT else v_FF))
        (if opp then (if b then v_TT else v_TF) else (if b then v_FT else v_FF))
  sign_refl i p a := by simp [intSign]
  sign_antisym i p a b := by
    simp only [intSign, Sign.flip]
    split_ifs <;> first | rfl | omega
  sign_trans i p a b c := by
    intro hab hbc; simp only [] at *
    split_ifs at * <;> exact intSign_trans _ _ _ hab hbc
  sign_irrel i p q a b h := by
    have : p (1 - i) = q (1 - i) := h (1 - i) (by intro heq; exact absurd heq (by omega))
    simp only [this]

-- Prisoner's Dilemma: C = true, D = false
def genPD := game2x2 3 0 5 1 3 5 0 1

theorem genPD_nash_DD : genPD.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem genPD_not_nash_CC : ¬genPD.IsPureNash (fun _ => true) := by
  intro h; have := h 0 false; revert this; decide

-- Matching Pennies: H = true, T = false
def genMP := game2x2 1 0 0 1 0 1 1 0

theorem genMP_no_pureNash : ∀ p : PureProfile (Fin 2) (fun _ : Fin 2 => Bool),
    ¬genMP.IsPureNash p := by
  intro p hp
  -- Specialize to get contradictory sign conditions
  -- Player 0 comparing (p 0) to false, and player 1 comparing (p 1) to false
  have h0f := hp 0 false
  have h1f := hp 1 false
  -- Unfold: genMP.sign i p (p i) false uses opp = p (1 - i)
  -- For player 0: opp = p 1; for player 1: opp = p 0
  unfold SignGame.IsPureNash at hp
  -- Key insight: use `show` to convert the sign to a concrete computation
  -- after specializing at concrete i values
  have h0t := hp 0 true
  have h1t := hp 1 true
  -- Now case split and use `simp` with concrete player indices
  -- After cases on p 0 / p 1, we have concrete Bool values
  -- but `p (1 - 0)` and `p (1 - 1)` need reducing
  -- Use `conv` or direct `change` to help
  have opp0 : p ((1 : Fin 2) - 0) = p 1 := congr_arg p (by decide)
  have opp1 : p ((1 : Fin 2) - 1) = p 0 := congr_arg p (by decide)
  -- Rewrite in hypotheses h0f, h1f, h0t, h1t
  simp only [genMP, game2x2, opp0, opp1, intSign, Sign.nonneg] at h0f h1f h0t h1t
  -- Now hypotheses should only mention p 0 and p 1 (not p (1-i))
  cases h0 : p 0 <;> cases h1 : p 1 <;> simp_all

-- Stag Hunt: S = true, H = false
def genSH := game2x2 4 0 3 3 4 3 0 3

theorem genSH_nash_SS : genSH.IsPureNash (fun _ => true) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem genSH_nash_HH : genSH.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

-- Battle of the Sexes: O = true, F = false
def genBoS := game2x2 3 0 0 2 2 0 0 3

theorem genBoS_nash_OO : genBoS.IsPureNash (fun _ => true) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem genBoS_nash_FF : genBoS.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

-- ================================================================
-- 3-player coordination game example
-- ================================================================

/-- A 3-player coordination game where each player has two actions (Bool).
    Each player gets payoff 1 if all agree, 0 otherwise.
    Sign is computed directly for decidability. -/
def coordGame3 : SignGame (Fin 3) (fun _ : Fin 3 => Bool) where
  sign i p a b :=
    -- Whether all agree when player i plays x (x = a or b)
    let agree (x : Bool) : Bool :=
      (if (0 : Fin 3) = i then x else p 0) == (if (1 : Fin 3) = i then x else p 1) &&
      (if (1 : Fin 3) = i then x else p 1) == (if (2 : Fin 3) = i then x else p 2)
    let payA : Int := if agree a then 1 else 0
    let payB : Int := if agree b then 1 else 0
    intSign payA payB
  sign_refl i p a := by simp [intSign]
  sign_antisym i p a b := by
    simp only [intSign, Sign.flip]; split_ifs <;> first | rfl | omega
  sign_trans i p a b c := by
    intro hab hbc; simp only [] at *
    split_ifs at * <;> exact intSign_trans _ _ _ hab hbc
  sign_irrel i p q a b h := by
    -- The agree function only uses p j for j ≠ i (otherwise uses a/b)
    -- When j ≠ i, h gives p j = q j, so agree is the same
    suffices ∀ x : Bool,
      ((if (0 : Fin 3) = i then x else p 0) == (if (1 : Fin 3) = i then x else p 1) &&
       (if (1 : Fin 3) = i then x else p 1) == (if (2 : Fin 3) = i then x else p 2)) =
      ((if (0 : Fin 3) = i then x else q 0) == (if (1 : Fin 3) = i then x else q 1) &&
       (if (1 : Fin 3) = i then x else q 1) == (if (2 : Fin 3) = i then x else q 2)) by
      simp only [intSign, this]
    intro x
    have h0 : (0 : Fin 3) ≠ i → p 0 = q 0 := fun hi => h 0 hi
    have h1 : (1 : Fin 3) ≠ i → p 1 = q 1 := fun hi => h 1 hi
    have h2 : (2 : Fin 3) ≠ i → p 2 = q 2 := fun hi => h 2 hi
    by_cases h0i : (0 : Fin 3) = i <;> by_cases h1i : (1 : Fin 3) = i <;>
      by_cases h2i : (2 : Fin 3) = i <;> simp_all

theorem coordGame3_nash_allTrue : coordGame3.IsPureNash (fun _ => true) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem coordGame3_nash_allFalse : coordGame3.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem coordGame3_not_nash_mixed :
    ¬coordGame3.IsPureNash (fun i : Fin 3 => if i = 0 then true else false) := by
  intro h; have := h 0 false; revert this; decide

-- ================================================================
-- Pedagogical examples
-- ================================================================

/-- The Prisoner's Dilemma has a unique Nash equilibrium at (D,D).
    Here is the deviation graph: each non-Nash profile has a player
    who can strictly improve by switching.

    (C,C) ──player 0 deviates──→ (D,C)
      │                            │
    player 1 deviates          player 1 deviates
      ↓                            ↓
    (C,D) ──player 0 deviates──→ (D,D) ← Nash: no deviations out -/
theorem genPD_unique_pureNash :
    ∀ p : PureProfile (Fin 2) (fun _ : Fin 2 => Bool),
    genPD.IsPureNash p ↔ p = (fun _ => false) := by
  intro p
  constructor
  · intro hp
    by_contra h
    -- If p ≠ (fun _ => false), some player plays true (cooperates)
    -- and can deviate to false (defect) for a better payoff
    have : ∃ i, p i = true := by
      by_contra hall; push_neg at hall
      apply h; ext i; exact Bool.eq_false_iff.mpr (hall i)
    obtain ⟨i, hi⟩ := this
    have hpi := hp i false; have hpi' := hp i true
    fin_cases i <;> (cases h0 : p 0 <;> cases h1 : p 1 <;>
      simp_all [genPD, game2x2, intSign, Sign.nonneg])
  · rintro rfl; exact genPD_nash_DD

/-- Matching Pennies: the only Nash equilibrium is the fully mixed profile
    where both players play {H, T}. We show:
    (1) No pure profile is Nash (genMP_no_pureNash above)
    (2) The fully mixed profile IS Nash -/
theorem genMP_mixed_nash : genMP.IsNash (fun _ : Fin 2 => Face.full (V := Bool)) := by
  intro i A
  -- Need: ¬StrictDev i σ A where σ = fun _ => full
  -- StrictDev = DevFaceLE i σ A (σ i) ∧ ¬DevFaceLE i σ (σ i) A
  -- DevFaceLE i σ A {true, false} means:
  --   ∀ a ∈ A, ∀ p (opponents play anything), ∀ b ∈ {T,F}, sign(a,b) ≥ 0
  -- This fails: for any a, there's an opponent choice making !a beat a.
  intro ⟨hfwd, _⟩
  obtain ⟨a, ha⟩ := A.2
  -- a ∈ A, so hfwd gives: sign(a, b) ≥ 0 for all opponent choices and b ∈ {T,F}
  -- Take b = !a and two different opponents to get a contradiction
  have h1 := hfwd a ha (fun _ => true) (fun _ _ => Finset.mem_univ _)
    (!a) (Finset.mem_univ _)
  have h2 := hfwd a ha (fun _ => false) (fun _ _ => Finset.mem_univ _)
    (!a) (Finset.mem_univ _)
  -- Each case (i=0/1, a=T/F) gives contradictory sign constraints
  fin_cases i <;> cases a <;> simp_all [genMP, game2x2, intSign, Sign.nonneg]

/-- The DevFaceLE ordering is partial on mixed profiles: in Matching Pennies,
    neither {H} nor {T} dominates the other when the opponent mixes. -/
theorem genMP_partial_order :
    let σ : Profile (Fin 2) (fun _ : Fin 2 => Bool) := fun _ => Face.full
    ¬genMP.DevFaceLE 0 σ (Face.vertex true) (Face.vertex false) ∧
    ¬genMP.DevFaceLE 0 σ (Face.vertex false) (Face.vertex true) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- H doesn't dominate T: when opponent plays T (false), T beats H for player 0
    have := h true (Finset.mem_singleton_self _)
      (fun _ => false) (fun _ _ => Finset.mem_univ _)
      false (Finset.mem_singleton_self _)
    simp_all [genMP, game2x2, intSign, Sign.nonneg]
  · -- T doesn't dominate H: when opponent plays H (true), H beats T for player 0
    have := h false (Finset.mem_singleton_self _)
      (fun _ => true) (fun _ _ => Finset.mem_univ _)
      true (Finset.mem_singleton_self _)
    simp_all [genMP, game2x2, intSign, Sign.nonneg]

-- ================================================================
-- Readable game constructors (for the article)
-- ================================================================

/-- Build a symmetric 2-player game from a ranking function.
    rank(myAction, oppAction) assigns a preference rank to each outcome.
    Higher rank = more preferred. Only the ordering matters — any two
    ranking functions with the same ordering produce the same game. -/
def symGame2x2 (rank : Bool → Bool → ℕ) :
    SignGame (Fin 2) (fun _ : Fin 2 => Bool) where
  sign i p a b :=
    let opp := p (1 - i)
    cmpSign (rank b opp) (rank a opp)
  sign_refl i p a := by simp [cmpSign_self]
  sign_antisym i p a b := by rw [cmpSign_flip]
  sign_trans i p a b c h1 h2 := cmpSign_trans h2 h1
  sign_irrel i p q a b h := by
    have : p (1 - i) = q (1 - i) := h (1 - i) (by intro heq; exact absurd heq (by omega))
    simp only [this]

/-- Build an asymmetric 2-player game from per-player ranking functions. -/
def game2x2_rank (rank₀ rank₁ : Bool → Bool → ℕ) :
    SignGame (Fin 2) (fun _ : Fin 2 => Bool) where
  sign i p a b :=
    let opp := p (1 - i)
    if (i : ℕ) = 0 then cmpSign (rank₀ b opp) (rank₀ a opp)
    else cmpSign (rank₁ b opp) (rank₁ a opp)
  sign_refl i p a := by split_ifs <;> simp [cmpSign_self]
  sign_antisym i p a b := by split_ifs <;> rw [cmpSign_flip]
  sign_trans i p a b c h1 h2 := by
    simp only [] at *; split_ifs at * <;> exact cmpSign_trans h2 h1
  sign_irrel i p q a b h := by
    have : p (1 - i) = q (1 - i) := h (1 - i) (by intro heq; exact absurd heq (by omega))
    simp only [this]

-- ================================================================
-- Prisoner's Dilemma (readable version)
-- ================================================================

/-- Prisoner's Dilemma ranking. C = true, D = false.
    Each player ranks outcomes (from their own perspective):
      CD < DD < CC < DC
    "If I cooperate and they defect, that's the worst.
     If we both defect, that's bad but not the worst.
     If we both cooperate, that's good.
     If I defect and they cooperate, that's the best." -/
def pd_rank (me opp : Bool) : ℕ :=
  match me, opp with
  | true,  false => 0   -- I cooperate, they defect (worst)
  | false, false => 1   -- both defect
  | true,  true  => 2   -- both cooperate
  | false, true  => 3   -- I defect, they cooperate (best)

/-- The PD is symmetric: both players have the same ranking. -/
def genPD' := symGame2x2 pd_rank

theorem genPD'_nash_DD : genPD'.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem genPD'_not_nash_CC : ¬genPD'.IsPureNash (fun _ => true) := by
  intro h; have := h 0 false; revert this; decide

/-- The numbers are just labels for the ranking.
    Any other numbers with the same ordering produce the same game. -/
def pd_rank_alt (me opp : Bool) : ℕ :=
  match me, opp with
  | true,  false => 10
  | false, false => 20
  | true,  true  => 30
  | false, true  => 40

theorem pd_same_game :
    (symGame2x2 pd_rank).sign = (symGame2x2 pd_rank_alt).sign := by
  ext i p a b
  simp only [symGame2x2, pd_rank, pd_rank_alt, cmpSign]
  cases a <;> cases b <;> cases (p (1 - i)) <;> simp

-- ================================================================
-- Matching Pennies (readable version)
-- ================================================================

/-- Matching Pennies. H = true, T = false.
    Player 0 wants to match: HH and TT are good, HT and TH are bad.
    Player 1 wants to differ: HT and TH are good, HH and TT are bad. -/
def genMP' := game2x2_rank
  (fun me opp => match me, opp with  -- P0 wants to match
    | true,  true  => 1
    | false, false => 1
    | _,     _     => 0)
  (fun me opp => match me, opp with  -- P1 wants to differ
    | true,  false => 1
    | false, true  => 1
    | _,     _     => 0)

theorem genMP'_no_pureNash :
    ∀ p, ¬genMP'.IsPureNash p := by
  intro p hp
  have h0t := hp 0 true; have h0f := hp 0 false
  have h1t := hp 1 true; have h1f := hp 1 false
  simp only [genMP', game2x2_rank, SignGame.IsPureNash, cmpSign, Sign.nonneg] at *
  cases h0 : p 0 <;> cases h1 : p 1 <;> simp_all

end Base
