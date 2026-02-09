import SyntheticGameTheory
import SyntheticGameTheory.DeviationGraph

namespace SyntheticGameTheory

open Game

-- ================================================================
-- Two-player two-action game infrastructure
-- ================================================================

/-- Build a 2x2 game from payoff values.
    Players are `Fin 2`, actions are `Bool`.
    u-values are player 0's payoffs, v-values are player 1's.
    Indices: first action = player 0's (Bool), second = player 1's (Bool).
    E.g. u₀₁ = player 0's payoff when 0 plays true, 1 plays false. -/
def game2x2 (u₀₀ u₀₁ u₁₀ u₁₁ : Int) (v₀₀ v₀₁ v₁₀ v₁₁ : Int) :
    Game (Fin 2) (fun _ => Bool) where
  pref := fun i p q =>
    let pay (r : PureProfile (Fin 2) (fun _ => Bool)) :=
      if i.val = 0 then
        if r 0 = true then (if r 1 = true then u₀₀ else u₀₁)
          else (if r 1 = true then u₁₀ else u₁₁)
      else
        if r 0 = true then (if r 1 = true then v₀₀ else v₀₁)
          else (if r 1 = true then v₁₀ else v₁₁)
    pay p ≥ pay q
  pref_preorder := fun _ => {
    refl := fun _ => le_refl _
    trans := fun {_ _ _} h1 h2 => le_trans h2 h1
  }
  pref_total := fun _ => ⟨fun _ _ => by simp only [ge_iff_le]; exact le_total _ _⟩
  pref_decidable := fun _ _ _ => inferInstance

/-- Make a pure profile from two booleans. -/
@[simp] def mkProfile (a b : Bool) : PureProfile (Fin 2) (fun _ => Bool) :=
  fun i => if i = 0 then a else b

@[simp] theorem mkProfile_zero (a b : Bool) : mkProfile a b 0 = a := by
  simp [mkProfile]

@[simp] theorem mkProfile_one (a b : Bool) : mkProfile a b 1 = b := by
  simp [mkProfile, show (1 : Fin 2) ≠ 0 from by omega]

/-- Every 2x2 profile equals mkProfile of its components. -/
theorem profile_eq (p : PureProfile (Fin 2) (fun _ => Bool)) :
    p = mkProfile (p 0) (p 1) := by
  funext i; simp only [mkProfile]
  have : i = 0 ∨ i = 1 := by have := i.isLt; omega
  rcases this with rfl | rfl <;> simp

-- Bool.eq_false_or_eq_true : b = true ∨ b = false
-- So rcases gives: inl = true, inr = false

-- ================================================================
-- Prisoner's Dilemma
-- ================================================================

/-- Prisoner's Dilemma. C = true, D = false.
    Payoffs: (C,C)→(3,3), (C,D)→(0,5), (D,C)→(5,0), (D,D)→(1,1) -/
def PD := game2x2 3 0 5 1 3 5 0 1

/-- (D,D) is the unique pure Nash equilibrium of PD. -/
theorem PD_nash_DD : PD.IsPureNash (mkProfile false false) := by
  intro i v; simp only [PD, game2x2, Function.update]
  cases v <;> simp_all <;> split_ifs <;> omega

/-- (C,C) is not Nash -- each player wants to defect. -/
theorem PD_not_nash_CC : ¬PD.IsPureNash (mkProfile true true) := by
  intro hp; have h := hp 0 false
  simp only [PD, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
  simp at h

/-- (C,D) is not Nash -- player 0 wants to defect. -/
theorem PD_not_nash_CD : ¬PD.IsPureNash (mkProfile true false) := by
  intro hp; have h := hp 0 false
  simp only [PD, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
  simp at h

/-- (D,C) is not Nash -- player 1 wants to defect. -/
theorem PD_not_nash_DC : ¬PD.IsPureNash (mkProfile false true) := by
  intro hp; have h := hp 1 false
  simp only [PD, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
  simp at h

/-- (C,C) is Pareto-optimal in PD. -/
theorem PD_pareto_CC : PD.IsParetoOptimal (mkProfile true true) := by
  intro q ⟨hw, i, hstrict⟩
  simp only [PD, WeakPareto, game2x2] at hw hstrict
  rcases Bool.eq_false_or_eq_true (q 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (q 1) with h1 | h1 <;> simp_all

/-- (D,D) is NOT Pareto-optimal -- (C,C) strictly dominates it. -/
theorem PD_not_pareto_DD : ¬PD.IsParetoOptimal (mkProfile false false) := by
  intro h; apply h (mkProfile true true)
  refine ⟨fun i => ?_, ⟨0, fun h => ?_⟩⟩
  · dsimp only [PD, game2x2]; simp only [mkProfile_zero, mkProfile_one]
    split_ifs <;> omega
  · revert h; dsimp only [PD, game2x2]; simp

-- ================================================================
-- Matching Pennies
-- ================================================================

/-- Matching Pennies. H = true, T = false.
    Player 0 wants to match, player 1 wants to mismatch.
    Payoffs: (H,H)→(1,0), (H,T)→(0,1), (T,H)→(0,1), (T,T)→(1,0) -/
def MP := game2x2 1 0 0 1 0 1 1 0

/-- Matching Pennies has no pure Nash equilibrium. -/
theorem MP_no_pureNash : ∀ p, ¬MP.IsPureNash p := by
  intro p hp; rw [profile_eq p] at hp
  rcases Bool.eq_false_or_eq_true (p 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (p 1) with h1 | h1 <;>
    simp only [h0, h1] at hp
  -- (H,H): player 1 prefers T (payoff 0→1)
  · have h := hp 1 false
    simp only [MP, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
    simp at h
  -- (H,T): player 0 prefers T (payoff 0→1)
  · have h := hp 0 false
    simp only [MP, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
    simp at h
  -- (T,H): player 0 prefers H (payoff 0→1)
  · have h := hp 0 true
    simp only [MP, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
    simp at h
  -- (T,T): player 1 prefers H (payoff 0→1)
  · have h := hp 1 true
    simp only [MP, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
    simp at h

/-- Matching Pennies is competitive: every profile lies on a cycle.
    The cycle is HH → HT → TT → TH → HH
    (1 deviates, 0 deviates, 1 deviates, 0 deviates). -/
theorem MP_competitive : MP.IsCompetitive := by
  intro p; rw [profile_eq p]
  rcases Bool.eq_false_or_eq_true (p 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (p 1) with h1 | h1 <;>
    simp only [h0, h1]
  -- (H,H): 1→T gives (H,T), cycle (H,T)→(T,T)→(T,H)→(H,H)
  · refine ⟨mkProfile true false,
      ⟨1, fun j hj => by simp [mkProfile]; omega,
          by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩, ?_⟩
    apply @Relation.TransGen.tail _ _ _ (mkProfile false true)
    · apply @Relation.TransGen.tail _ _ _ (mkProfile false false)
      · exact Relation.TransGen.single
          ⟨0, fun j hj => by simp [mkProfile]; omega,
              by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
      · exact ⟨1, fun j hj => by simp [mkProfile]; omega,
                by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
    · exact ⟨0, fun j hj => by simp [mkProfile]; omega,
              by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
  -- (H,T): 0→T gives (T,T), cycle (T,T)→(T,H)→(H,H)→(H,T)
  · refine ⟨mkProfile false false,
      ⟨0, fun j hj => by simp [mkProfile]; omega,
          by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩, ?_⟩
    apply @Relation.TransGen.tail _ _ _ (mkProfile true true)
    · apply @Relation.TransGen.tail _ _ _ (mkProfile false true)
      · exact Relation.TransGen.single
          ⟨1, fun j hj => by simp [mkProfile]; omega,
              by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
      · exact ⟨0, fun j hj => by simp [mkProfile]; omega,
                by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
    · exact ⟨1, fun j hj => by simp [mkProfile]; omega,
              by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
  -- (T,H): 0→H gives (H,H), cycle (H,H)→(H,T)→(T,T)→(T,H)
  · refine ⟨mkProfile true true,
      ⟨0, fun j hj => by simp [mkProfile]; omega,
          by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩, ?_⟩
    apply @Relation.TransGen.tail _ _ _ (mkProfile false false)
    · apply @Relation.TransGen.tail _ _ _ (mkProfile true false)
      · exact Relation.TransGen.single
          ⟨1, fun j hj => by simp [mkProfile]; omega,
              by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
      · exact ⟨0, fun j hj => by simp [mkProfile]; omega,
                by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
    · exact ⟨1, fun j hj => by simp [mkProfile]; omega,
              by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
  -- (T,T): 1→H gives (T,H), cycle (T,H)→(H,H)→(H,T)→(T,T)
  · refine ⟨mkProfile false true,
      ⟨1, fun j hj => by simp [mkProfile]; omega,
          by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩, ?_⟩
    apply @Relation.TransGen.tail _ _ _ (mkProfile true false)
    · apply @Relation.TransGen.tail _ _ _ (mkProfile true true)
      · exact Relation.TransGen.single
          ⟨0, fun j hj => by simp [mkProfile]; omega,
              by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
      · exact ⟨1, fun j hj => by simp [mkProfile]; omega,
                by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩
    · exact ⟨0, fun j hj => by simp [mkProfile]; omega,
              by simp only [MP, game2x2, mkProfile_zero, mkProfile_one]; simp⟩

-- ================================================================
-- Stag Hunt
-- ================================================================

/-- Stag Hunt. S = true, H = false.
    Payoffs: (S,S)→(4,4), (S,H)→(0,3), (H,S)→(3,0), (H,H)→(3,3) -/
def SH := game2x2 4 0 3 3 4 3 0 3

/-- (S,S) is a Nash equilibrium of Stag Hunt. -/
theorem SH_nash_SS : SH.IsPureNash (mkProfile true true) := by
  intro i v; simp only [SH, game2x2, Function.update]
  cases v <;> simp_all <;> split_ifs <;> omega

/-- (H,H) is a Nash equilibrium of Stag Hunt. -/
theorem SH_nash_HH : SH.IsPureNash (mkProfile false false) := by
  intro i v; simp only [SH, game2x2, Function.update]
  cases v <;> simp_all <;> split_ifs <;> omega

/-- (S,H) is not Nash -- player 0 wants to switch to H. -/
theorem SH_not_nash_SH : ¬SH.IsPureNash (mkProfile true false) := by
  intro hp; have h := hp 0 false
  simp only [SH, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
  simp at h

/-- (H,S) is not Nash -- player 1 wants to switch to H. -/
theorem SH_not_nash_HS : ¬SH.IsPureNash (mkProfile false true) := by
  intro hp; have h := hp 1 false
  simp only [SH, game2x2, Function.update, mkProfile_zero, mkProfile_one] at h
  simp at h

/-- (S,S) weakly Pareto-dominates (H,H). -/
theorem SH_SS_weakPareto_HH :
    SH.WeakPareto (mkProfile true true) (mkProfile false false) := by
  intro i; dsimp only [SH, game2x2]
  simp only [mkProfile_zero, mkProfile_one]; split_ifs <;> omega

/-- (S,S) strictly Pareto-dominates (H,H). -/
theorem SH_SS_strictPareto_HH :
    SH.StrictPareto (mkProfile true true) (mkProfile false false) :=
  ⟨SH_SS_weakPareto_HH, ⟨0, fun h => by revert h; dsimp only [SH, game2x2]; simp⟩⟩

/-- (S,S) is Pareto-optimal. -/
theorem SH_pareto_SS : SH.IsParetoOptimal (mkProfile true true) := by
  intro q ⟨hw, i, hstrict⟩
  simp only [SH, WeakPareto, game2x2] at hw hstrict
  rcases Bool.eq_false_or_eq_true (q 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (q 1) with h1 | h1 <;> simp_all

/-- (H,H) is NOT Pareto-optimal -- dominated by (S,S). -/
theorem SH_not_pareto_HH : ¬SH.IsParetoOptimal (mkProfile false false) :=
  fun h => h _ SH_SS_strictPareto_HH

end SyntheticGameTheory
