import SyntheticGameTheory.Basic
import SyntheticGameTheory.Pareto
import SyntheticGameTheory.Program.ProgramGame
import SyntheticGameTheory.Program.GuardedTree

/-!
# Program Equilibrium Examples

Concrete demonstrations using the Prisoner's Dilemma:

1. **Level 0**: standard PD — (D,D) is the unique pure Nash
2. **Level 1**: conditional cooperation — TFT-like programs achieve (C,C)
3. **Patching obstruction**: at any level, fixed strategies can be improved
4. **Compactification**: level truncation restores Nash existence
-/

namespace SyntheticGameTheory

-- ================================================================
-- Infrastructure: 2x2 game with Bool players
-- ================================================================

/-- Build a 2x2 game with `Bool` players and `Bool` actions.
    `true` = cooperate, `false` = defect.
    Payoff indices: first = player `true`'s action, second = player `false`'s. -/
def boolGame2x2 (u₀₀ u₀₁ u₁₀ u₁₁ : Int) (v₀₀ v₀₁ v₁₀ v₁₁ : Int) :
    Game Bool (fun _ => Bool) where
  pref := fun b p q =>
    let pay (r : PureProfile Bool (fun _ => Bool)) :=
      if b = true then
        if r true = true then (if r false = true then u₀₀ else u₀₁)
          else (if r false = true then u₁₀ else u₁₁)
      else
        if r true = true then (if r false = true then v₀₀ else v₀₁)
          else (if r false = true then v₁₀ else v₁₁)
    pay p ≥ pay q
  pref_preorder := fun _ => {
    refl := fun _ => le_refl _
    trans := fun {_ _ _} h1 h2 => le_trans h2 h1
  }
  pref_total := fun _ => ⟨fun _ _ => by simp only [ge_iff_le]; exact le_total _ _⟩
  pref_decidable := fun _ _ _ => inferInstance

/-- Pure profile from two booleans for Bool-indexed players. -/
@[simp] def mkBoolProfile (a b : Bool) : PureProfile Bool (fun _ => Bool) :=
  fun i => if i = true then a else b

@[simp] theorem mkBoolProfile_true (a b : Bool) : mkBoolProfile a b true = a := by
  simp [mkBoolProfile]

@[simp] theorem mkBoolProfile_false (a b : Bool) : mkBoolProfile a b false = b := by
  simp [mkBoolProfile]

/-- Every Bool-indexed 2x2 profile equals mkBoolProfile of its components. -/
theorem boolProfile_eq (p : PureProfile Bool (fun _ => Bool)) :
    p = mkBoolProfile (p true) (p false) := by
  funext b; cases b <;> simp [mkBoolProfile]

-- ================================================================
-- Section 1: PD at Level 0
-- ================================================================

/-- Prisoner's Dilemma with Bool players. C = true, D = false.
    Payoffs: (C,C)→(3,3), (C,D)→(0,5), (D,C)→(5,0), (D,D)→(1,1) -/
def boolPD := boolGame2x2 3 0 5 1 3 5 0 1

/-- (D,D) is a pure Nash equilibrium of PD. -/
theorem boolPD_nash_DD : boolPD.IsPureNash (mkBoolProfile false false) := by
  intro b v; simp only [boolPD, boolGame2x2, Function.update]
  cases v <;> cases b <;> simp_all

/-- (C,C) is not Nash. -/
theorem boolPD_not_nash_CC : ¬boolPD.IsPureNash (mkBoolProfile true true) := by
  intro hp; have h := hp true false
  simp only [boolPD, boolGame2x2, Function.update, mkBoolProfile_true, mkBoolProfile_false] at h
  simp at h

-- ================================================================
-- Section 2: PD at Level 1 — Conditional Cooperation
-- ================================================================

/-- At level 0, a program is just an action. The level-0 PD is the standard PD. -/
theorem level0_is_standard :
    ∀ (o : Oracle (fun _ => Bool)) (a b : Bool),
    evalLevel o 0 a b = mkPP a b := fun _ _ _ => rfl

/-- TFT-like program at level 1 for player `true`:
    "cooperate if opponent cooperates, defect otherwise." -/
def tft_true : Prog (fun _ => Bool) true 1 :=
  show (Bool → Bool) from fun opp_action => opp_action

/-- TFT for player `false`: same logic. -/
def tft_false : Prog (fun _ => Bool) false 1 :=
  show (Bool → Bool) from fun opp_action => opp_action

/-- Always-defect at level 1 for player `true`. -/
def alwaysD_true : Prog (fun _ => Bool) true 1 :=
  show (Bool → Bool) from fun _ => false

/-- With a cooperating oracle, TFT vs TFT evaluates to (C,C). -/
theorem tft_vs_tft_CC :
    evalLevel ⟨fun _ => true⟩ 1 tft_true tft_false = mkPP true true := by
  simp [evalLevel, tft_true, tft_false, Prog.restrict]

/-- With a cooperating oracle, AlwaysD vs TFT evaluates to (D,D). -/
theorem alwaysD_vs_tft :
    evalLevel ⟨fun _ => true⟩ 1 alwaysD_true tft_false = mkPP false false := by
  simp [evalLevel, alwaysD_true, tft_false, Prog.restrict]

/-- TFT achieves a better outcome than AlwaysD against TFT opponents (for player true).
    TFT vs TFT gives payoff 3 (mutual cooperation), while AlwaysD vs TFT gives payoff 1. -/
theorem tft_beats_alwaysD :
    ¬boolPD.pref true
      (evalLevel ⟨fun _ => true⟩ 1 alwaysD_true tft_false)
      (evalLevel ⟨fun _ => true⟩ 1 tft_true tft_false) := by
  simp [evalLevel, tft_true, tft_false, alwaysD_true, Prog.restrict, mkPP,
        boolPD, boolGame2x2]

-- ================================================================
-- Section 3: The Patching Obstruction
-- ================================================================

/-- At any level k, the tree game over PD has a (mixed) Nash equilibrium —
    but we show that specific pure profiles can always be improved. -/
theorem treeGame_PD_nash_exists (o : Oracle (fun _ => Bool)) (k : ℕ) :
    ∃ σ, (treeGame boolPD o k).IsNash σ :=
  treeGame_nash_exists boolPD o k

/-- Helper: a level-0 program in `ProgUnion` from an action. -/
def progAtom (b : Bool) (v : Bool) : ProgUnion (fun _ => Bool) b :=
  ⟨0, (show Prog (fun _ => Bool) b 0 from v)⟩

theorem level0_patchable_CC :
    ¬boolPD.pref true
      ((oracleCompletion (V := fun _ => Bool) ⟨fun _ => true⟩).complete
        (fun b => progAtom b true))
      ((oracleCompletion (V := fun _ => Bool) ⟨fun _ => true⟩).complete
        (Function.update (fun b => progAtom b true) true (progAtom true false))) := by
  simp only [oracleCompletion, Function.update, progAtom, evalLevel, boolPD, boolGame2x2]
  decide

-- ================================================================
-- Section 4: Compactification Restores Nash
-- ================================================================

/-- Nash equilibrium exists at every level k of the PD tree game.
    This is the compactification principle: finite program spaces
    always admit Nash equilibria. -/
theorem PD_tree_nash_at_level (k : ℕ) :
    ∃ σ, (treeGame boolPD ⟨fun _ => true⟩ k).IsNash σ :=
  treeGame_nash_exists boolPD ⟨fun _ => true⟩ k

end SyntheticGameTheory
