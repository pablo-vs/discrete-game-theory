import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import SyntheticGameTheory.Unified

namespace GeneralUnified

open Unified (Sign Face cmpSign)

-- ================================================================
-- Section 1: Reuse Sign and Face from Unified
-- ================================================================

-- Sign, Sign.nonneg, Sign.flip, Sign.mul, cmpSign are imported from Unified
-- Face, Face.vertex, Face.full, Face.IsSubface, Face.ext are imported from Unified

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
noncomputable def ofPayoffs [Fintype I]
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
private def intSign (a b : Int) : Sign :=
  if a > b then .pos
  else if a = b then .zero
  else .neg

private theorem intSign_refl (a : Int) : intSign a a = .zero := by
  simp [intSign]

private theorem intSign_antisym (a b : Int) : intSign a b = (intSign b a).flip := by
  simp only [intSign, Sign.flip]; split_ifs <;> first | rfl | omega

private theorem intSign_trans (a b c : Int) :
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

end GeneralUnified
