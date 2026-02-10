import SyntheticGameTheory
import SyntheticGameTheory.DeviationGraph
import SyntheticGameTheory.ProgramGame
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-!
# Guarded Tree Model for Program Equilibrium

Concrete presheaf model where programs at level `k+1` can inspect opponent
programs at level `k`, but same-level evaluation is circular. An oracle
(anchor) resolves the circularity by providing a level-0 default.

Players are indexed by `Bool` (`true` = player 0, `false` = player 1),
so the opponent `!b` satisfies `!!b = b` definitionally.

Key constructions:
- `Prog V b k`: program type at level `k` for player `b`
- `Oracle`: level-0 anchor resolving circularity
- `Prog.embed` / `Prog.restrict`: lift/project between adjacent levels
- `evalLevel`: evaluation using restriction for cross-level application
- `treeGame`: the game at each level, inheriting Nash existence
-/

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: Program Types
-- ================================================================

/-- Programs at level `k` for player `b`.
    Level 0: just an action (pure strategy).
    Level k+1: a function from opponent's level-k program to own action. -/
def Prog (V : Bool → Type) (b : Bool) : ℕ → Type
  | 0 => V b
  | k + 1 => Prog V (!b) k → V b

variable {V : Bool → Type} [∀ b, DecidableEq (V b)] [∀ b, Fintype (V b)]

/-- Combined `DecidableEq × Fintype` instance, resolving mutual dependency. -/
noncomputable def Prog.instances (b : Bool) :
    ∀ k, DecidableEq (Prog V b k) × Fintype (Prog V b k)
  | 0 => ⟨inferInstanceAs (DecidableEq (V b)), inferInstanceAs (Fintype (V b))⟩
  | k + 1 =>
    haveI : DecidableEq (Prog V (!b) k) := (Prog.instances (!b) k).1
    haveI : Fintype (Prog V (!b) k) := (Prog.instances (!b) k).2
    ⟨show DecidableEq (Prog V (!b) k → V b) from inferInstance,
     show Fintype (Prog V (!b) k → V b) from inferInstance⟩

noncomputable instance Prog.instDecidableEq (b : Bool) (k : ℕ) :
    DecidableEq (Prog V b k) :=
  (Prog.instances b k).1

noncomputable instance Prog.instFintype (b : Bool) (k : ℕ) :
    Fintype (Prog V b k) :=
  (Prog.instances b k).2

instance Prog.instNonempty [∀ b, Nonempty (V b)] (b : Bool) :
    ∀ k, Nonempty (Prog V b k)
  | 0 => inferInstanceAs (Nonempty (V b))
  | k + 1 => show Nonempty (Prog V (!b) k → V b) from
    haveI := Prog.instNonempty (!b) k; inferInstance

-- ================================================================
-- Section 2: Oracle, Embed, and Restrict
-- ================================================================

/-- An oracle provides a level-0 default action for each player.
    This resolves the circularity of same-level evaluation. -/
structure Oracle (V : Bool → Type) where
  anchor : ∀ b, V b

mutual
  def Prog.embed (o : Oracle V) : ∀ (b : Bool) (k : ℕ), Prog V b k → Prog V b (k + 1)
    | _, 0, v => show Prog V _ 0 → V _ from fun _ => v
    | b, k + 1, f =>
      show Prog V (!b) (k + 1) → V b from
      fun opp_prog => f (Prog.restrict o (!b) k opp_prog)

  def Prog.restrict (o : Oracle V) :
      ∀ (b : Bool) (k : ℕ), Prog V b (k + 1) → Prog V b k
    | _, 0, f => show V _ from (show V (!_) → V _ from f) (o.anchor _)
    | b, k + 1, f =>
      show Prog V (!b) k → V b from
      fun opp_prog =>
        (show Prog V (!b) (k + 1) → V b from f)
          (Prog.embed o (!b) k opp_prog)
end

-- ================================================================
-- Section 3: Evaluation
-- ================================================================

/-- Make a pure profile for `Bool`-indexed players from two values. -/
def mkPP (v0 : V true) (v1 : V false) : PureProfile Bool V
  | true => v0
  | false => v1

omit [∀ b, DecidableEq (V b)] [∀ b, Fintype (V b)] in
@[simp] theorem mkPP_true (v0 : V true) (v1 : V false) : mkPP v0 v1 true = v0 := rfl

omit [∀ b, DecidableEq (V b)] [∀ b, Fintype (V b)] in
@[simp] theorem mkPP_false (v0 : V true) (v1 : V false) : mkPP v0 v1 false = v1 := rfl

/-- Evaluate level-k programs using the oracle.
    Each player applies their function to the opponent's program
    restricted down one level. At level 0, just pair the actions. -/
def evalLevel (o : Oracle V) :
    ∀ k, Prog V true k → Prog V false k → PureProfile Bool V
  | 0, v0, v1 => mkPP v0 v1
  | k + 1, f0, f1 =>
    mkPP
      ((show Prog V false k → V true from f0) (Prog.restrict o false k f1))
      ((show Prog V true k → V false from f1) (Prog.restrict o true k f0))

-- ================================================================
-- Section 4: Level-k Game and Nash Existence
-- ================================================================

/-- The game at level k: players choose level-k programs, outcomes
    evaluated via the oracle. -/
noncomputable def treeGame (G : Game Bool V) (o : Oracle V) (k : ℕ) :
    Game Bool (fun b => Prog V b k) where
  pref b p q := G.pref b (evalLevel o k (p true) (p false))
                          (evalLevel o k (q true) (q false))
  pref_preorder b := {
    refl := fun _ => (G.pref_preorder b).refl _
    trans := fun {_ _ _} h1 h2 => (G.pref_preorder b).toIsTrans.trans _ _ _ h1 h2
  }
  pref_total b := ⟨fun _ _ => (G.pref_total b).total _ _⟩
  pref_decidable b _ _ := G.pref_decidable b _ _

/-- Nash equilibrium exists at every level of the tree game. -/
theorem treeGame_nash_exists [∀ b, Nonempty (V b)]
    (G : Game Bool V) (o : Oracle V) (k : ℕ) :
    ∃ σ, (treeGame G o k).IsNash σ :=
  (treeGame G o k).nash_exists

-- ================================================================
-- Section 5: Building EvalWorld from Trees
-- ================================================================

/-- The union of all program levels for a player. -/
def ProgUnion (V : Bool → Type) (b : Bool) := Σ k, Prog V b k

/-- The tree evaluation world: programs are level-tagged, evaluation is
    defined when programs are at the same level. -/
def treeEvalWorld (V : Bool → Type) [∀ b, DecidableEq (V b)] [∀ b, Fintype (V b)]
    (o : Oracle V) : EvalWorld Bool V where
  C b := ProgUnion V b
  eval c :=
    let ⟨k0, p0⟩ := c true
    let ⟨k1, p1⟩ := c false
    if h : k0 = k1 then
      some (evalLevel o k0 p0 (h ▸ p1))
    else
      none

/-- An oracle completion for the tree evaluation world: when levels differ,
    use the oracle's anchor to produce a default outcome. When they match,
    use normal evaluation. -/
noncomputable def oracleCompletion (o : Oracle V) : Completion (treeEvalWorld V o) where
  complete c :=
    let ⟨k0, p0⟩ := c true
    let ⟨k1, p1⟩ := c false
    if h : k0 = k1 then
      evalLevel o k0 p0 (h ▸ p1)
    else
      -- Levels differ: fall back to oracle's anchor
      mkPP (o.anchor true) (o.anchor false)
  consistent c r heval := by
    unfold treeEvalWorld at heval
    simp only at heval ⊢
    generalize c true = ct at heval ⊢
    generalize c false = cf at heval ⊢
    obtain ⟨k0, p0⟩ := ct
    obtain ⟨k1, p1⟩ := cf
    simp only at heval ⊢
    split at heval
    · rename_i h
      simp only [Option.some.injEq] at heval
      simp only [dite_true, h, heval]
    · simp at heval

-- ================================================================
-- Section 6: The Diagonal — Same-Level Circularity
-- ================================================================

omit [∀ b, DecidableEq (V b)] [∀ b, Fintype (V b)] in
/-- At level 1, evaluation applies each player's function to the opponent's
    action after restricting through the oracle (extracting the anchor). -/
theorem evalLevel_one (o : Oracle V) (f0 : Prog V true 1) (f1 : Prog V false 1) :
    evalLevel o 1 f0 f1 =
      mkPP (f0 (Prog.restrict o false 0 f1)) (f1 (Prog.restrict o true 0 f0)) :=
  rfl

omit [∀ b, DecidableEq (V b)] [∀ b, Fintype (V b)] in
/-- At level 0, restriction extracts the anchor: a level-1 program applied
    to the oracle's anchor gives a pure action. -/
theorem restrict_zero (o : Oracle V) (b : Bool) (f : Prog V b 1) :
    Prog.restrict o b 0 f = (show V (!b) → V b from f) (o.anchor (!b)) :=
  rfl

end SyntheticGameTheory
