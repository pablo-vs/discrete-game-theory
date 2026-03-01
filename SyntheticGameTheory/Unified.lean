import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Unified

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
-- Section 2: Faces (nonempty finite subsets)
-- ================================================================

@[reducible]
def Face (V : Type*) [DecidableEq V] := { S : Finset V // S.Nonempty }

namespace Face

variable {V : Type*} [DecidableEq V]

def vertex (v : V) : Face V :=
  ⟨{v}, Finset.singleton_nonempty v⟩

def full [Fintype V] [Nonempty V] : Face V :=
  ⟨Finset.univ, Finset.univ_nonempty⟩

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
-- Section 3: SignGame
-- ================================================================

structure SignGame (V₀ V₁ : Type*) [DecidableEq V₀] [DecidableEq V₁] where
  sign₀ : V₁ → V₀ → V₀ → Sign
  sign₁ : V₀ → V₁ → V₁ → Sign
  sign₀_refl : ∀ j a, sign₀ j a a = .zero
  sign₁_refl : ∀ j a, sign₁ j a a = .zero
  sign₀_antisym : ∀ j a b, sign₀ j a b = (sign₀ j b a).flip
  sign₁_antisym : ∀ j a b, sign₁ j a b = (sign₁ j b a).flip
  sign₀_trans : ∀ j a b c, (sign₀ j a b).nonneg → (sign₀ j b c).nonneg →
    (sign₀ j a c).nonneg
  sign₁_trans : ∀ j a b c, (sign₁ j a b).nonneg → (sign₁ j b c).nonneg →
    (sign₁ j a c).nonneg

namespace SignGame

variable {V₀ V₁ : Type*} [DecidableEq V₀] [DecidableEq V₁]
variable (G : SignGame V₀ V₁)

-- ================================================================
-- Section 4: DevFaceLE
-- ================================================================

/-- A weakly dominates B against opponents in F:
    ∀ a ∈ A, j ∈ F, b ∈ B, sign₀ j a b ≥ 0. -/
def DevFaceLE₀ (F₁ : Face V₁) (A B : Face V₀) : Prop :=
  ∀ a ∈ A.1, ∀ j ∈ F₁.1, ∀ b ∈ B.1, (G.sign₀ j a b).nonneg

def DevFaceLE₁ (F₀ : Face V₀) (A B : Face V₁) : Prop :=
  ∀ a ∈ A.1, ∀ j ∈ F₀.1, ∀ b ∈ B.1, (G.sign₁ j a b).nonneg

-- Monotonicity: all one-liners
theorem DevFaceLE₀_antitone {F₁ F₁' : Face V₁} (h : Face.IsSubface F₁ F₁')
    {A B : Face V₀} (hle : G.DevFaceLE₀ F₁' A B) : G.DevFaceLE₀ F₁ A B :=
  fun a ha j hj b hb => hle a ha j (h hj) b hb

theorem DevFaceLE₀_left_mono {F₁ : Face V₁} {A A' B : Face V₀}
    (h : Face.IsSubface A A') (hle : G.DevFaceLE₀ F₁ A' B) : G.DevFaceLE₀ F₁ A B :=
  fun a ha j hj b hb => hle a (h ha) j hj b hb

theorem DevFaceLE₀_right_mono {F₁ : Face V₁} {A B B' : Face V₀}
    (h : Face.IsSubface B B') (hle : G.DevFaceLE₀ F₁ A B') : G.DevFaceLE₀ F₁ A B :=
  fun a ha j hj b hb => hle a ha j hj b (h hb)

theorem DevFaceLE₁_antitone {F₀ F₀' : Face V₀} (h : Face.IsSubface F₀ F₀')
    {A B : Face V₁} (hle : G.DevFaceLE₁ F₀' A B) : G.DevFaceLE₁ F₀ A B :=
  fun a ha j hj b hb => hle a ha j (h hj) b hb

theorem DevFaceLE₁_left_mono {F₀ : Face V₀} {A A' B : Face V₁}
    (h : Face.IsSubface A A') (hle : G.DevFaceLE₁ F₀ A' B) : G.DevFaceLE₁ F₀ A B :=
  fun a ha j hj b hb => hle a (h ha) j hj b hb

theorem DevFaceLE₁_right_mono {F₀ : Face V₀} {A B B' : Face V₁}
    (h : Face.IsSubface B B') (hle : G.DevFaceLE₁ F₀ A B') : G.DevFaceLE₁ F₀ A B :=
  fun a ha j hj b hb => hle a ha j hj b (h hb)

-- Transitivity
theorem DevFaceLE₀_trans {F₁ : Face V₁} {A B C : Face V₀}
    (hAB : G.DevFaceLE₀ F₁ A B) (hBC : G.DevFaceLE₀ F₁ B C) :
    G.DevFaceLE₀ F₁ A C := by
  intro a ha j hj c hc
  obtain ⟨b, hb⟩ := B.2
  exact G.sign₀_trans j a b c (hAB a ha j hj b hb) (hBC b hb j hj c hc)

theorem DevFaceLE₁_trans {F₀ : Face V₀} {A B C : Face V₁}
    (hAB : G.DevFaceLE₁ F₀ A B) (hBC : G.DevFaceLE₁ F₀ B C) :
    G.DevFaceLE₁ F₀ A C := by
  intro a ha j hj c hc
  obtain ⟨b, hb⟩ := B.2
  exact G.sign₁_trans j a b c (hAB a ha j hj b hb) (hBC b hb j hj c hc)

-- ================================================================
-- Section 5: StrictDev, Nash, Better
-- ================================================================

/-- A strictly dominates current face σ.1 against opponents σ.2. -/
def StrictDev₀ (σ : Face V₀ × Face V₁) (A : Face V₀) : Prop :=
  G.DevFaceLE₀ σ.2 A σ.1 ∧ ¬G.DevFaceLE₀ σ.2 σ.1 A

def StrictDev₁ (σ : Face V₀ × Face V₁) (A : Face V₁) : Prop :=
  G.DevFaceLE₁ σ.1 A σ.2 ∧ ¬G.DevFaceLE₁ σ.1 σ.2 A

def IsNash (σ : Face V₀ × Face V₁) : Prop :=
  (∀ A : Face V₀, ¬G.StrictDev₀ σ A) ∧
  (∀ A : Face V₁, ¬G.StrictDev₁ σ A)

def Better₀ (F₁ : Face V₁) (A B : Face V₀) : Prop :=
  G.DevFaceLE₀ F₁ A B ∧ ¬G.DevFaceLE₀ F₁ B A

theorem Better₀_irref (F₁ : Face V₁) (A : Face V₀) : ¬G.Better₀ F₁ A A :=
  fun ⟨h, hn⟩ => hn h

theorem Better₀_trans {F₁ : Face V₁} {A B C : Face V₀}
    (hAB : G.Better₀ F₁ A B) (hBC : G.Better₀ F₁ B C) : G.Better₀ F₁ A C :=
  ⟨G.DevFaceLE₀_trans hAB.1 hBC.1, fun hCA => hAB.2 (G.DevFaceLE₀_trans hBC.1 hCA)⟩

-- ================================================================
-- Section 6: OutsideDominated
-- ================================================================

/-- Every included action dominates every excluded action. -/
def OutsideDominated₀ (σ : Face V₀ × Face V₁) : Prop :=
  ∀ v, v ∉ σ.1.1 → ∀ w, w ∈ σ.1.1 →
    G.DevFaceLE₀ σ.2 (Face.vertex w) (Face.vertex v)

def OutsideDominated₁ (σ : Face V₀ × Face V₁) : Prop :=
  ∀ v, v ∉ σ.2.1 → ∀ w, w ∈ σ.2.1 →
    G.DevFaceLE₁ σ.1 (Face.vertex w) (Face.vertex v)

-- ================================================================
-- Section 7: OutsideDominated base case
-- ================================================================

variable [Fintype V₀] [Fintype V₁]

theorem OutsideDominated₀_maximal [Nonempty V₀] [Nonempty V₁] :
    G.OutsideDominated₀ (Face.full, Face.full) :=
  fun v hv => absurd (Finset.mem_univ v) hv

theorem OutsideDominated₁_maximal [Nonempty V₀] [Nonempty V₁] :
    G.OutsideDominated₁ (Face.full, Face.full) :=
  fun v hv => absurd (Finset.mem_univ v) hv

-- ================================================================
-- Section 8: OutsideDominated preservation
-- ================================================================

omit [Fintype V₀] [Fintype V₁] in
/-- When player 0 restricts to A ⊆ σ.1 with A dominating σ.1,
    OutsideDominated₀ is preserved. -/
theorem OutsideDominated₀_preserved
    {σ : Face V₀ × Face V₁} {A : Face V₀}
    (h_inv : G.OutsideDominated₀ σ)
    (h_sub : Face.IsSubface A σ.1)
    (h_dev : G.DevFaceLE₀ σ.2 A σ.1) :
    G.OutsideDominated₀ (A, σ.2) := by
  intro v hv w hw
  by_cases hv_in : v ∈ σ.1.1
  · -- v newly excluded: was in σ.1, not in A
    -- A dominates σ.1, vertex w ⊆ A, vertex v ⊆ σ.1
    -- left-mono + right-mono gives vertex w dominates vertex v
    exact G.DevFaceLE₀_right_mono
      (show Face.IsSubface (Face.vertex v) σ.1 from Finset.singleton_subset_iff.mpr hv_in)
      (G.DevFaceLE₀_left_mono
        (show Face.IsSubface (Face.vertex w) A from Finset.singleton_subset_iff.mpr hw)
        h_dev)
  · -- v was already outside σ.1
    exact h_inv v hv_in w (h_sub hw)

omit [Fintype V₀] [Fintype V₁] in
/-- When player 0 restricts, OutsideDominated₁ is preserved by antitonicity. -/
theorem OutsideDominated₁_preserved_by_player0
    {σ : Face V₀ × Face V₁} {A : Face V₀}
    (h_inv : G.OutsideDominated₁ σ)
    (h_sub : Face.IsSubface A σ.1) :
    G.OutsideDominated₁ (A, σ.2) := by
  intro v hv w hw
  exact G.DevFaceLE₁_antitone h_sub (h_inv v hv w hw)

-- Symmetric versions
omit [Fintype V₀] [Fintype V₁] in
theorem OutsideDominated₁_preserved
    {σ : Face V₀ × Face V₁} {A : Face V₁}
    (h_inv : G.OutsideDominated₁ σ)
    (h_sub : Face.IsSubface A σ.2)
    (h_dev : G.DevFaceLE₁ σ.1 A σ.2) :
    G.OutsideDominated₁ (σ.1, A) := by
  intro v hv w hw
  by_cases hv_in : v ∈ σ.2.1
  · exact G.DevFaceLE₁_right_mono
      (show Face.IsSubface (Face.vertex v) σ.2 from Finset.singleton_subset_iff.mpr hv_in)
      (G.DevFaceLE₁_left_mono
        (show Face.IsSubface (Face.vertex w) A from Finset.singleton_subset_iff.mpr hw)
        h_dev)
  · exact h_inv v hv_in w (h_sub hw)

omit [Fintype V₀] [Fintype V₁] in
theorem OutsideDominated₀_preserved_by_player1
    {σ : Face V₀ × Face V₁} {A : Face V₁}
    (h_inv : G.OutsideDominated₀ σ)
    (h_sub : Face.IsSubface A σ.2) :
    G.OutsideDominated₀ (σ.1, A) := by
  intro v hv w hw
  exact G.DevFaceLE₀_antitone h_sub (h_inv v hv w hw)

-- ================================================================
-- Section 9: Restricting deviations
-- ================================================================

omit [Fintype V₀] [Fintype V₁] in
/-- Key lemma: the backward-direction witness is in σ.1. -/
private theorem outsideDom₀_witness_mem
    {σ : Face V₀ × Face V₁}
    (h_inv : G.OutsideDominated₀ σ)
    (h_neg : ¬G.DevFaceLE₀ σ.2 σ.1 A) :
    ∃ a ∈ σ.1.1, ∃ j ∈ σ.2.1, ∃ b ∈ A.1, ¬(G.sign₀ j a b).nonneg ∧ b ∈ σ.1.1 := by
  simp only [DevFaceLE₀] at h_neg; push_neg at h_neg
  obtain ⟨a, ha, j, hj, b, hb, hn⟩ := h_neg
  by_cases hb_σ : b ∈ σ.1.1
  · exact ⟨a, ha, j, hj, b, hb, hn, hb_σ⟩
  · -- b ∉ σ.1 ⟹ OutsideDom gives vertex a dominates vertex b ⟹ contradiction
    exact absurd (h_inv b hb_σ a ha a (Finset.mem_singleton_self _) j hj
      b (Finset.mem_singleton_self _)) hn

omit [Fintype V₀] [Fintype V₁] in
/-- When OutsideDominated₀ holds and player 0 has a strict deviation to A,
    there exists a restricting strict deviation to A ∩ σ.1. -/
theorem exists_restrictingStrictDev₀
    {σ : Face V₀ × Face V₁} {A : Face V₀}
    (h_inv : G.OutsideDominated₀ σ)
    (h_dev : G.StrictDev₀ σ A) :
    ∃ A' : Face V₀,
      G.StrictDev₀ σ A' ∧ Face.IsSubface A' σ.1 ∧ A' ≠ σ.1 := by
  obtain ⟨h_fwd, h_bwd⟩ := h_dev
  obtain ⟨a, ha_σ, j, hj, b, hb_A, hn, hb_σ⟩ := G.outsideDom₀_witness_mem h_inv h_bwd
  -- A' = A ∩ σ.1, nonempty since b ∈ A ∩ σ.1
  let A' : Face V₀ := ⟨A.1 ∩ σ.1.1, ⟨b, Finset.mem_inter.mpr ⟨hb_A, hb_σ⟩⟩⟩
  refine ⟨A', ⟨?_, ?_⟩, Finset.inter_subset_right, ?_⟩
  · -- Forward: A' dominates σ.1 (A' ⊆ A, use left-mono)
    exact G.DevFaceLE₀_left_mono Finset.inter_subset_left h_fwd
  · -- Backward: σ.1 doesn't dominate A'
    intro h_contra
    have hb' : b ∈ A'.1 := Finset.mem_inter.mpr ⟨hb_A, hb_σ⟩
    exact absurd (h_contra a ha_σ j hj b hb') hn
  · -- A' ≠ σ.1
    intro heq
    have h_σ_sub_A : Face.IsSubface σ.1 A := by
      intro x hx; have := (heq ▸ hx : x ∈ A'.1)
      exact (Finset.mem_inter.mp this).1
    apply h_bwd
    intro x hx j' hj' y hy
    by_cases hy_σ : y ∈ σ.1.1
    · -- y ∈ σ.1: use DevFaceLE σ.1 σ.1 (from left-mono of h_fwd with σ.1 ⊆ A)
      exact (G.DevFaceLE₀_left_mono h_σ_sub_A h_fwd) x hx j' hj' y hy_σ
    · -- y ∉ σ.1: OutsideDom gives vertex x dominates vertex y
      exact h_inv y hy_σ x hx x (Finset.mem_singleton_self _) j' hj' y (Finset.mem_singleton_self _)

-- Symmetric for player 1
omit [Fintype V₀] [Fintype V₁] in
private theorem outsideDom₁_witness_mem
    {σ : Face V₀ × Face V₁}
    (h_inv : G.OutsideDominated₁ σ)
    (h_neg : ¬G.DevFaceLE₁ σ.1 σ.2 A) :
    ∃ a ∈ σ.2.1, ∃ j ∈ σ.1.1, ∃ b ∈ A.1, ¬(G.sign₁ j a b).nonneg ∧ b ∈ σ.2.1 := by
  simp only [DevFaceLE₁] at h_neg; push_neg at h_neg
  obtain ⟨a, ha, j, hj, b, hb, hn⟩ := h_neg
  by_cases hb_σ : b ∈ σ.2.1
  · exact ⟨a, ha, j, hj, b, hb, hn, hb_σ⟩
  · exact absurd (h_inv b hb_σ a ha a (Finset.mem_singleton_self _) j hj
      b (Finset.mem_singleton_self _)) hn

omit [Fintype V₀] [Fintype V₁] in
theorem exists_restrictingStrictDev₁
    {σ : Face V₀ × Face V₁} {A : Face V₁}
    (h_inv : G.OutsideDominated₁ σ)
    (h_dev : G.StrictDev₁ σ A) :
    ∃ A' : Face V₁,
      G.StrictDev₁ σ A' ∧ Face.IsSubface A' σ.2 ∧ A' ≠ σ.2 := by
  obtain ⟨h_fwd, h_bwd⟩ := h_dev
  obtain ⟨a, ha_σ, j, hj, b, hb_A, hn, hb_σ⟩ := G.outsideDom₁_witness_mem h_inv h_bwd
  let A' : Face V₁ := ⟨A.1 ∩ σ.2.1, ⟨b, Finset.mem_inter.mpr ⟨hb_A, hb_σ⟩⟩⟩
  refine ⟨A', ⟨?_, ?_⟩, Finset.inter_subset_right, ?_⟩
  · exact G.DevFaceLE₁_left_mono Finset.inter_subset_left h_fwd
  · intro h_contra
    have hb' : b ∈ A'.1 := Finset.mem_inter.mpr ⟨hb_A, hb_σ⟩
    exact absurd (h_contra a ha_σ j hj b hb') hn
  · intro heq
    have h_σ_sub_A : Face.IsSubface σ.2 A := by
      intro x hx; exact (Finset.mem_inter.mp (heq ▸ hx)).1
    apply h_bwd
    intro x hx j' hj' y hy
    by_cases hy_σ : y ∈ σ.2.1
    · exact (G.DevFaceLE₁_left_mono h_σ_sub_A h_fwd) x hx j' hj' y hy_σ
    · exact h_inv y hy_σ x hx x (Finset.mem_singleton_self _) j' hj' y (Finset.mem_singleton_self _)

-- ================================================================
-- Section 10: Profile size and descent
-- ================================================================

def profileSize (σ : Face V₀ × Face V₁) : ℕ := σ.1.1.card + σ.2.1.card

omit [Fintype V₀] [Fintype V₁] in
theorem profileSize_decreases₀ {σ : Face V₀ × Face V₁} {A : Face V₀}
    (hsub : Face.IsSubface A σ.1) (hne : A ≠ σ.1) :
    profileSize (A, σ.2) < profileSize σ := by
  simp only [profileSize]
  have : A.1.card < σ.1.1.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (Face.ext h)⟩)
  omega

omit [Fintype V₀] [Fintype V₁] in
theorem profileSize_decreases₁ {σ : Face V₀ × Face V₁} {A : Face V₁}
    (hsub : Face.IsSubface A σ.2) (hne : A ≠ σ.2) :
    profileSize (σ.1, A) < profileSize σ := by
  simp only [profileSize]
  have : A.1.card < σ.2.1.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (Face.ext h)⟩)
  omega

-- ================================================================
-- Section 11: Nash existence
-- ================================================================

omit [Fintype V₀] [Fintype V₁] in
private theorem nash_exists_aux
    (σ : Face V₀ × Face V₁)
    (h₀ : G.OutsideDominated₀ σ)
    (h₁ : G.OutsideDominated₁ σ) :
    ∃ τ : Face V₀ × Face V₁, G.IsNash τ := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h⟩
  · simp only [IsNash, not_and_or, not_forall, not_not] at h
    rcases h with ⟨A, hA⟩ | ⟨A, hA⟩
    · obtain ⟨A', hdev, hsub, hne⟩ := G.exists_restrictingStrictDev₀ h₀ hA
      have := profileSize_decreases₀ hsub hne
      exact nash_exists_aux (A', σ.2)
        (G.OutsideDominated₀_preserved h₀ hsub hdev.1)
        (G.OutsideDominated₁_preserved_by_player0 h₁ hsub)
    · obtain ⟨A', hdev, hsub, hne⟩ := G.exists_restrictingStrictDev₁ h₁ hA
      have := profileSize_decreases₁ hsub hne
      exact nash_exists_aux (σ.1, A')
        (G.OutsideDominated₀_preserved_by_player1 h₀ hsub)
        (G.OutsideDominated₁_preserved h₁ hsub hdev.1)
termination_by profileSize σ

theorem nash_exists [Nonempty V₀] [Nonempty V₁] :
    ∃ σ : Face V₀ × Face V₁, G.IsNash σ :=
  G.nash_exists_aux (Face.full, Face.full) G.OutsideDominated₀_maximal G.OutsideDominated₁_maximal

omit [Fintype V₀] [Fintype V₁] in
/-- Strengthened Nash existence with all invariants: Nash, subface, and
    OutsideDominated are all preserved through the descent. -/
theorem nash_exists_sub_OD
    (σ : Face V₀ × Face V₁)
    (h₀ : G.OutsideDominated₀ σ)
    (h₁ : G.OutsideDominated₁ σ) :
    ∃ τ : Face V₀ × Face V₁,
      G.IsNash τ ∧ Face.IsSubface τ.1 σ.1 ∧ Face.IsSubface τ.2 σ.2 ∧
      G.OutsideDominated₀ τ ∧ G.OutsideDominated₁ τ := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h, fun x hx => hx, fun x hx => hx, h₀, h₁⟩
  · simp only [IsNash, not_and_or, not_forall, not_not] at h
    rcases h with ⟨A, hA⟩ | ⟨A, hA⟩
    · obtain ⟨A', hdev, hsub, hne⟩ := G.exists_restrictingStrictDev₀ h₀ hA
      have := profileSize_decreases₀ hsub hne
      have h₀' := G.OutsideDominated₀_preserved h₀ hsub hdev.1
      have h₁' := G.OutsideDominated₁_preserved_by_player0 h₁ hsub
      obtain ⟨τ, hτN, hτ₀, hτ₁, hτOD₀, hτOD₁⟩ := nash_exists_sub_OD (A', σ.2) h₀' h₁'
      exact ⟨τ, hτN, fun x hx => hsub (hτ₀ hx), hτ₁, hτOD₀, hτOD₁⟩
    · obtain ⟨A', hdev, hsub, hne⟩ := G.exists_restrictingStrictDev₁ h₁ hA
      have := profileSize_decreases₁ hsub hne
      have h₀' := G.OutsideDominated₀_preserved_by_player1 h₀ hsub
      have h₁' := G.OutsideDominated₁_preserved h₁ hsub hdev.1
      obtain ⟨τ, hτN, hτ₀, hτ₁, hτOD₀, hτOD₁⟩ := nash_exists_sub_OD (σ.1, A') h₀' h₁'
      exact ⟨τ, hτN, hτ₀, fun x hx => hsub (hτ₁ hx), hτOD₀, hτOD₁⟩
  termination_by profileSize σ

omit [Fintype V₀] [Fintype V₁] in
/-- Strengthened Nash existence: starting from σ with OutsideDominated,
    there exists a Nash subprofile (both components are subfaces of σ). -/
theorem nash_exists_sub
    (σ : Face V₀ × Face V₁)
    (h₀ : G.OutsideDominated₀ σ)
    (h₁ : G.OutsideDominated₁ σ) :
    ∃ τ : Face V₀ × Face V₁,
      G.IsNash τ ∧ Face.IsSubface τ.1 σ.1 ∧ Face.IsSubface τ.2 σ.2 := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h, fun x hx => hx, fun x hx => hx⟩
  · simp only [IsNash, not_and_or, not_forall, not_not] at h
    rcases h with ⟨A, hA⟩ | ⟨A, hA⟩
    · obtain ⟨A', hdev, hsub, hne⟩ := G.exists_restrictingStrictDev₀ h₀ hA
      have := profileSize_decreases₀ hsub hne
      obtain ⟨τ, hτ_nash, hτ₀, hτ₁⟩ := nash_exists_sub (A', σ.2)
        (G.OutsideDominated₀_preserved h₀ hsub hdev.1)
        (G.OutsideDominated₁_preserved_by_player0 h₁ hsub)
      exact ⟨τ, hτ_nash, fun x hx => hsub (hτ₀ hx), hτ₁⟩
    · obtain ⟨A', hdev, hsub, hne⟩ := G.exists_restrictingStrictDev₁ h₁ hA
      have := profileSize_decreases₁ hsub hne
      obtain ⟨τ, hτ_nash, hτ₀, hτ₁⟩ := nash_exists_sub (σ.1, A')
        (G.OutsideDominated₀_preserved_by_player1 h₀ hsub)
        (G.OutsideDominated₁_preserved h₁ hsub hdev.1)
      exact ⟨τ, hτ_nash, hτ₀, fun x hx => hsub (hτ₁ hx)⟩
  termination_by profileSize σ

-- ================================================================
-- Section 12: Building SignGame from payoffs
-- ================================================================

set_option linter.unnecessarySeqFocus false in
def ofPayoffs (u : V₀ → V₁ → Int) (v : V₀ → V₁ → Int) : SignGame V₀ V₁ where
  sign₀ j a b :=
    if u a j > u b j then .pos
    else if u a j = u b j then .zero
    else .neg
  sign₁ j a b :=
    if v j a > v j b then .pos
    else if v j a = v j b then .zero
    else .neg
  sign₀_refl j a := by simp
  sign₁_refl j a := by simp
  sign₀_antisym j a b := by
    simp only [Sign.flip]
    split_ifs <;> first | rfl | omega
  sign₁_antisym j a b := by
    simp only [Sign.flip]
    split_ifs <;> first | rfl | omega
  sign₀_trans j a b c := by
    simp only [Sign.nonneg]
    split_ifs <;> simp_all <;> omega
  sign₁_trans j a b c := by
    simp only [Sign.nonneg]
    split_ifs <;> simp_all <;> omega

-- ================================================================
-- Section 13: Pure Nash and examples
-- ================================================================

/-- Pure Nash: no player can improve by switching. -/
def IsPureNash (p : V₀ × V₁) : Prop :=
  (∀ v : V₀, (G.sign₀ p.2 p.1 v).nonneg) ∧
  (∀ v : V₁, (G.sign₁ p.1 p.2 v).nonneg)

end SignGame

-- ================================================================
-- 2×2 game examples
-- ================================================================

def game2x2 (u_TT u_TF u_FT u_FF : Int) (v_TT v_TF v_FT v_FF : Int) :
    SignGame Bool Bool :=
  SignGame.ofPayoffs
    (fun a b => if a then (if b then u_TT else u_TF) else (if b then u_FT else u_FF))
    (fun a b => if a then (if b then v_TT else v_TF) else (if b then v_FT else v_FF))

-- Prisoner's Dilemma: C = true, D = false
def PD := game2x2 3 0 5 1 3 5 0 1

theorem PD_nash_DD : PD.IsPureNash (false, false) := by
  constructor <;> intro v <;> cases v <;> decide

theorem PD_not_nash_CC : ¬PD.IsPureNash (true, true) := by
  intro ⟨h, _⟩; have := h false; revert this; decide

-- Matching Pennies: H = true, T = false
def MP := game2x2 1 0 0 1 0 1 1 0

theorem MP_no_pureNash : ∀ p : Bool × Bool, ¬MP.IsPureNash p := by
  intro ⟨a, b⟩ ⟨h₀, h₁⟩
  revert h₀ h₁; cases a <;> cases b <;> simp [MP, game2x2,
    SignGame.ofPayoffs, Sign.nonneg]

-- Stag Hunt: S = true, H = false
def SH := game2x2 4 0 3 3 4 3 0 3

theorem SH_nash_SS : SH.IsPureNash (true, true) := by
  constructor <;> intro v <;> cases v <;> decide

theorem SH_nash_HH : SH.IsPureNash (false, false) := by
  constructor <;> intro v <;> cases v <;> decide

-- Battle of the Sexes: O = true, F = false
def BoS := game2x2 3 0 0 2 2 0 0 3

theorem BoS_nash_OO : BoS.IsPureNash (true, true) := by
  constructor <;> intro v <;> cases v <;> decide

theorem BoS_nash_FF : BoS.IsPureNash (false, false) := by
  constructor <;> intro v <;> cases v <;> decide

end Unified
