import DiscreteGameTheory.Base

namespace Base

open SignGame

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
  have h0t := hp 0 true; have h0f := hp 0 false
  have h1t := hp 1 true; have h1f := hp 1 false
  simp only [genMP, game2x2, IsPureNash, intSign, Sign.nonneg] at *
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
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    fin_cases i <;> simp_all [intSign]

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

/-- The Prisoner's Dilemma has a unique Nash equilibrium at (D,D). -/
theorem genPD_unique_pureNash :
    ∀ p : PureProfile (Fin 2) (fun _ : Fin 2 => Bool),
    genPD.IsPureNash p ↔ p = (fun _ => false) := by
  intro p
  constructor
  · intro hp
    by_contra h
    have : ∃ i, p i = true := by
      by_contra hall; push_neg at hall
      apply h; ext i; exact Bool.eq_false_iff.mpr (hall i)
    obtain ⟨i, hi⟩ := this
    have hpi := hp i false; have hpi' := hp i true
    fin_cases i <;> (cases h0 : p 0 <;> cases h1 : p 1 <;>
      simp_all [genPD, game2x2, intSign, Sign.nonneg])
  · rintro rfl; exact genPD_nash_DD

/-- Matching Pennies: the only Nash equilibrium is the fully mixed profile
    where both players play {H, T}. -/
theorem genMP_mixed_nash : genMP.IsNash (fun _ : Fin 2 => Face.full (V := Bool)) := by
  intro i A
  intro ⟨hfwd, _⟩
  obtain ⟨a, ha⟩ := A.2
  have hcon : ∀ (p : ∀ _ : Fin 2, Bool),
      ConsistentAt (fun _ : Fin 2 => Face.full (V := Bool)) i p :=
    fun _ _ _ => Finset.mem_univ _
  have h1 := hfwd a ha (fun _ => true) (hcon _) (!a) (Finset.mem_univ _)
  have h2 := hfwd a ha (fun _ => false) (hcon _) (!a) (Finset.mem_univ _)
  fin_cases i <;> cases a <;> simp_all [genMP, game2x2, intSign, Sign.nonneg]

/-- The Dominates ordering is partial on mixed profiles: in Matching Pennies,
    neither {H} nor {T} dominates the other when the opponent mixes. -/
theorem genMP_partial_order :
    let σ : Profile (Fin 2) (fun _ : Fin 2 => Bool) := fun _ => Face.full
    ¬genMP.Dominates 0 σ (Face.vertex true) (Face.vertex false) ∧
    ¬genMP.Dominates 0 σ (Face.vertex false) (Face.vertex true) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h true (Finset.mem_singleton_self _) (fun _ => false)
      (fun _ _ => Finset.mem_univ _ : ConsistentAt _ (0 : Fin 2) _)
      false (Finset.mem_singleton_self _)
    simp_all [genMP, game2x2, intSign, Sign.nonneg]
  · have := h false (Finset.mem_singleton_self _) (fun _ => true)
      (fun _ _ => Finset.mem_univ _ : ConsistentAt _ (0 : Fin 2) _)
      true (Finset.mem_singleton_self _)
    simp_all [genMP, game2x2, intSign, Sign.nonneg]

-- ================================================================
-- Readable game constructors (for the article)
-- ================================================================

/-- Build a symmetric 2-player game from a ranking function. -/
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

/-- Prisoner's Dilemma ranking. C = true, D = false. -/
def pd_rank (me opp : Bool) : ℕ :=
  match me, opp with
  | true,  false => 0   -- I cooperate, they defect (worst)
  | false, false => 1   -- both defect
  | true,  true  => 2   -- both cooperate
  | false, true  => 3   -- I defect, they cooperate (best)

def genPD' := symGame2x2 pd_rank

theorem genPD'_nash_DD : genPD'.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem genPD'_not_nash_CC : ¬genPD'.IsPureNash (fun _ => true) := by
  intro h; have := h 0 false; revert this; decide

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
  simp only [genMP', game2x2_rank, IsPureNash, cmpSign, Sign.nonneg] at *
  cases h0 : p 0 <;> cases h1 : p 1 <;> simp_all

end Base
