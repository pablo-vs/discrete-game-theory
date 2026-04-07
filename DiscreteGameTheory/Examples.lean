import DiscreteGameTheory.Base

namespace Base

open SignGame

def intSign (a b : Int) : Sign :=
  if a > b then .pos
  else if a = b then .zero
  else .neg

lemma intSign_refl (a : Int) : intSign a a = .zero := by
  simp [intSign]

lemma intSign_antisym (a b : Int) : intSign a b = (intSign b a).flip := by
  simp only [intSign, Sign.flip]; split_ifs <;> first | rfl | omega

lemma intSign_trans (a b c : Int) :
    (intSign a b).nonneg → (intSign b c).nonneg → (intSign a c).nonneg := by
  simp only [intSign, Sign.nonneg]; split_ifs <;> simp_all; omega

/-- Construct a 2-player Bool game from payoff matrices.
    Uses `ofPayoffs` to get axioms for free. -/
def game2x2 (u_TT u_TF u_FT u_FF : Int) (v_TT v_TF v_FT v_FF : Int) :
    SignGame (Fin 2) (fun _ : Fin 2 => Bool) :=
  SignGame.ofPayoffs (fun i s =>
    if (i : ℕ) = 0 then
      if s 0 then (if s 1 then u_TT else u_TF) else (if s 1 then u_FT else u_FF)
    else
      if s 0 then (if s 1 then v_TT else v_TF) else (if s 1 then v_FT else v_FF))

-- Prisoner's Dilemma: C = true, D = false
def pd := game2x2 3 0 5 1 3 5 0 1

theorem pd_nash_DD : pd.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem pd_not_nash_CC : ¬pd.IsPureNash (fun _ => true) := by
  intro h; have := h 0 false; revert this; decide

-- Matching Pennies: H = true, T = false
def mp := game2x2 1 0 0 1 0 1 1 0

theorem mp_no_pureNash : ∀ p : PureProfile (Fin 2) (fun _ : Fin 2 => Bool),
    ¬mp.IsPureNash p := by
  intro p hp
  have h0t := hp 0 true; have h0f := hp 0 false
  have h1t := hp 1 true; have h1f := hp 1 false
  simp only [mp, game2x2, SignGame.ofPayoffs, IsPureNash, SignGame.signAction,
    Sign.nonneg, Function.update] at *
  cases h0 : p 0 <;> cases h1 : p 1 <;> simp_all

-- Stag Hunt: S = true, H = false
def sh := game2x2 4 0 3 3 4 3 0 3

theorem sh_nash_SS : sh.IsPureNash (fun _ => true) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem sh_nash_HH : sh.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

-- Battle of the Sexes: O = true, F = false
def bos := game2x2 3 0 0 2 2 0 0 3

theorem bos_nash_OO : bos.IsPureNash (fun _ => true) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem bos_nash_FF : bos.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

-- ================================================================
-- 3-player coordination game
-- ================================================================

/-- A 3-player coordination game: each player gets payoff 1 if all agree, 0 otherwise. -/
def coordGame3 : SignGame (Fin 3) (fun _ : Fin 3 => Bool) where
  sign _i p q :=
    let allAgree (s : ∀ _ : Fin 3, Bool) : Bool := s 0 == s 1 && s 1 == s 2
    let payP : Int := if allAgree p then 1 else 0
    let payQ : Int := if allAgree q then 1 else 0
    intSign payP payQ
  sign_refl _i p := by simp [intSign]
  sign_antisym _i p q := by
    simp only [intSign, Sign.flip]; split_ifs <;> first | rfl | omega
  sign_trans _i p q r := by
    intro hpq hqr; simp only [] at *
    split_ifs at * <;> exact intSign_trans _ _ _ hpq hqr

theorem coordGame3_nash_allTrue : coordGame3.IsPureNash (fun _ => true) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem coordGame3_nash_allFalse : coordGame3.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

theorem coordGame3_not_nash_mixed :
    ¬coordGame3.IsPureNash (fun i : Fin 3 => if i = 0 then true else false) := by
  intro h; have := h 0 false; revert this; decide

-- ================================================================
-- Pedagogical examples: uniqueness, mixed Nash, and dominance partiality
-- ================================================================

/-- The Prisoner's Dilemma has a unique pure Nash equilibrium at (D,D).
    This illustrates the central tension of PD: mutual cooperation is
    Pareto-better but not an equilibrium. -/
theorem pd_unique_pureNash :
    ∀ p : PureProfile (Fin 2) (fun _ : Fin 2 => Bool),
    pd.IsPureNash p ↔ p = (fun _ => false) := by
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
      simp_all [pd, game2x2, SignGame.ofPayoffs, SignGame.signAction, Sign.nonneg, Function.update])
  · rintro rfl; exact pd_nash_DD

/-- Matching Pennies has no pure Nash equilibrium (`mp_no_pureNash`), but the
    fully mixed profile where both players play {H, T} is a Nash equilibrium
    in the sign-game sense: no face strictly dominates the full face. -/
theorem mp_mixed_nash : mp.IsNash (fun _ : Fin 2 => Face.full (V := Bool)) := by
  intro i A ⟨hfwd, _⟩
  obtain ⟨a, ha⟩ := A.2
  have hcon : ∀ (p : ∀ _ : Fin 2, Bool),
      ConsistentAt (fun _ : Fin 2 => Face.full (V := Bool)) i p :=
    fun _ _ _ => Finset.mem_univ _
  have h1 := hfwd a ha (fun _ => true) (hcon _) (!a) (Finset.mem_univ _)
  have h2 := hfwd a ha (fun _ => false) (hcon _) (!a) (Finset.mem_univ _)
  fin_cases i <;> cases a <;> simp_all [mp, game2x2, SignGame.ofPayoffs, SignGame.signAction, Sign.nonneg, Function.update]

/-- The Dominates ordering is genuinely partial on mixed profiles: in Matching
    Pennies, when the opponent plays the full face {H,T}, neither {H} nor {T}
    dominates the other for player 0. This shows that sign-game dominance is
    not a total order on faces. -/
theorem mp_partial_order :
    let σ : Profile (Fin 2) (fun _ : Fin 2 => Bool) := fun _ => Face.full
    ¬mp.Dominates 0 σ (Face.vertex true) (Face.vertex false) ∧
    ¬mp.Dominates 0 σ (Face.vertex false) (Face.vertex true) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h true (Finset.mem_singleton_self _) (fun _ => false)
      (fun _ _ => Finset.mem_univ _ : ConsistentAt _ (0 : Fin 2) _)
      false (Finset.mem_singleton_self _)
    simp_all [mp, game2x2, SignGame.ofPayoffs, SignGame.signAction, Sign.nonneg, Function.update]
  · have := h false (Finset.mem_singleton_self _) (fun _ => true)
      (fun _ _ => Finset.mem_univ _ : ConsistentAt _ (0 : Fin 2) _)
      true (Finset.mem_singleton_self _)
    simp_all [mp, game2x2, SignGame.ofPayoffs, SignGame.signAction, Sign.nonneg, Function.update]

/-- Build a symmetric 2-player game from a ranking function.
    `rank me opp` gives the ordinal payoff when I play `me` and my opponent plays `opp`.
    Symmetry means both players share the same ranking function. -/
def symGame2x2 (rank : Bool → Bool → ℕ) :
    SignGame (Fin 2) (fun _ : Fin 2 => Bool) :=
  SignGame.ofPayoffs (fun i s => (rank (s i) (s (1 - i)) : Int))

/-- Build an asymmetric 2-player game from per-player ranking functions. -/
def game2x2_rank (rank₀ rank₁ : Bool → Bool → ℕ) :
    SignGame (Fin 2) (fun _ : Fin 2 => Bool) :=
  SignGame.ofPayoffs (fun i s =>
    if (i : ℕ) = 0 then (rank₀ (s 0) (s 1) : Int)
    else (rank₁ (s 1) (s 0) : Int))

-- Prisoner's Dilemma via ranking: C = true, D = false
def pd_rank (me opp : Bool) : ℕ :=
  match me, opp with
  | true,  false => 0   -- I cooperate, they defect (worst)
  | false, false => 1   -- both defect
  | true,  true  => 2   -- both cooperate
  | false, true  => 3   -- I defect, they cooperate (best)

def pd' := symGame2x2 pd_rank

lemma pd'_nash_DD : pd'.IsPureNash (fun _ => false) := by
  intro i v; fin_cases i <;> cases v <;> decide

lemma pd'_not_nash_CC : ¬pd'.IsPureNash (fun _ => true) := by
  intro h; have := h 0 false; revert this; decide

/-- Two ranking functions that differ by an affine transform produce the same
    sign function, illustrating ordinal invariance. -/
def pd_rank_alt (me opp : Bool) : ℕ :=
  match me, opp with
  | true,  false => 10
  | false, false => 20
  | true,  true  => 30
  | false, true  => 40

theorem pd_same_game :
    (symGame2x2 pd_rank).sign = (symGame2x2 pd_rank_alt).sign := by
  ext i p q
  simp only [symGame2x2, SignGame.ofPayoffs, pd_rank, pd_rank_alt]
  fin_cases i <;> (
    cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : q 0 <;> cases h3 : q 1 <;>
    simp_all)

-- Matching Pennies via ranking: P0 wants to match, P1 wants to differ
def mp' := game2x2_rank
  (fun me opp => match me, opp with  -- P0 wants to match
    | true,  true  => 1
    | false, false => 1
    | _,     _     => 0)
  (fun me opp => match me, opp with  -- P1 wants to differ
    | true,  false => 1
    | false, true  => 1
    | _,     _     => 0)

theorem mp'_no_pureNash :
    ∀ p, ¬mp'.IsPureNash p := by
  intro p hp
  have h0t := hp 0 true; have h0f := hp 0 false
  have h1t := hp 1 true; have h1f := hp 1 false
  simp only [mp', game2x2_rank, SignGame.ofPayoffs, SignGame.signAction,
    IsPureNash, Sign.nonneg, Function.update] at *
  cases h0 : p 0 <;> cases h1 : p 1 <;> simp_all

-- ================================================================
-- Executing the Nash descent: `findNash` computes an equilibrium
-- ================================================================

/-!
Unlike `nash_exists`, which is a pure existence theorem, `findNash` is a `def`
returning a concrete Nash profile. It runs the descent algorithm as a terminating
program, so we can `#eval` it to see the equilibrium.

Prisoner's Dilemma has a unique pure Nash equilibrium at (D, D). Running the
descent from the fully mixed profile `{C, D}²` converges there:
```
#eval (pd.findNash.1 0).1   -- {false}  (D for player 0)
#eval (pd.findNash.1 1).1   -- {false}  (D for player 1)
```

Matching Pennies has no pure Nash equilibrium, but the fully mixed profile is
an ordinal Nash equilibrium — no proper subface strictly dominates the full face.
The descent recognises this immediately and returns the starting profile:
```
#eval (mp.findNash.1 0).1   -- {false, true}
#eval (mp.findNash.1 1).1   -- {false, true}
```
-/

/-- The descent finds the unique pure Nash of the Prisoner's Dilemma. Since the
    whole algorithm is computable, `decide` discharges the claim by running it. -/
theorem pd_findNash_is_DD :
    (pd.findNash.1 0).1 = {false} ∧ (pd.findNash.1 1).1 = {false} := by
  native_decide

/-- The descent leaves Matching Pennies at the fully mixed profile — the ordinal
    Nash equilibrium. -/
theorem mp_findNash_is_full :
    (mp.findNash.1 0).1 = {false, true} ∧ (mp.findNash.1 1).1 = {false, true} := by
  native_decide

end Base
