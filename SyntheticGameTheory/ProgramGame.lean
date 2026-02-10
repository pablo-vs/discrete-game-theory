import SyntheticGameTheory
import SyntheticGameTheory.DeviationGraph

/-!
# Program Equilibrium — Core Axiomatics

Formalizes the key structures for program equilibrium:
- `EvalWorld`: a setting where agents have code spaces and a partial evaluator
- `Completion`: resolves partiality (e.g., via an oracle)
- `completionGame`: the induced game on program spaces
- `IsProgramNash`: Nash in the completion game
- `IsPatchable`: existence of a strict improvement (negation of Nash)
- Nash existence for finite program spaces via `nash_exists`
-/

namespace SyntheticGameTheory

-- ================================================================
-- Section 1: EvalWorld and Completion
-- ================================================================

/-- An evaluation world: each player has a code space, and there is a
    partial evaluator that may or may not produce a pure outcome. -/
structure EvalWorld (N : Type*) (V : N → Type*) where
  /-- Code space for each player. -/
  C : N → Type*
  /-- Partial evaluator: given programs for all players, may produce an outcome. -/
  eval : (∀ i, C i) → Option (PureProfile N V)

/-- A completion of an evaluation world: a total evaluator that agrees with
    the partial one wherever it is defined. -/
structure Completion {N : Type*} {V : N → Type*} (W : EvalWorld N V) where
  /-- Total evaluator: always produces an outcome. -/
  complete : (∀ i, W.C i) → PureProfile N V
  /-- Consistency: when `eval` returns `some`, `complete` agrees. -/
  consistent : ∀ c r, W.eval c = some r → complete c = r

-- ================================================================
-- Section 2: Completion Game
-- ================================================================

variable {N : Type*} [DecidableEq N]
variable {V : N → Type*} [∀ i, DecidableEq (V i)]

/-- The game induced by a completion of an evaluation world.
    Players choose programs; preferences are evaluated on completed outcomes. -/
noncomputable def completionGame (G : Game N V) (W : EvalWorld N V)
    [∀ i, DecidableEq (W.C i)]
    (comp : Completion W) : Game N (fun i => W.C i) where
  pref i p q := G.pref i (comp.complete p) (comp.complete q)
  pref_preorder i := {
    refl := fun _ => (G.pref_preorder i).refl _
    trans := fun {_ _ _} h1 h2 => (G.pref_preorder i).toIsTrans.trans _ _ _ h1 h2
  }
  pref_total i := ⟨fun _ _ => (G.pref_total i).total _ _⟩
  pref_decidable i _ _ := G.pref_decidable i _ _

/-- A program profile is a Nash equilibrium of the completion game. -/
def IsProgramNash (G : Game N V) (W : EvalWorld N V)
    [∀ i, DecidableEq (W.C i)]
    (comp : Completion W) (c : ∀ i, W.C i) : Prop :=
  (completionGame G W comp).IsPureNash c

-- ================================================================
-- Section 3: Nash Existence for Finite Program Spaces
-- ================================================================

/-- When program spaces are finite and nonempty, the completion game has
    a (mixed) Nash equilibrium. -/
theorem completionGame_nash_exists [Fintype N]
    (G : Game N V) (W : EvalWorld N V) (comp : Completion W)
    [∀ i, Fintype (W.C i)] [∀ i, DecidableEq (W.C i)] [∀ i, Nonempty (W.C i)] :
    ∃ σ, (completionGame G W comp).IsNash σ :=
  (completionGame G W comp).nash_exists

-- ================================================================
-- Section 4: Patchability (No-Nash Vocabulary)
-- ================================================================

/-- A program profile is patchable if some player has a strict improvement. -/
def IsPatchable (G : Game N V) (W : EvalWorld N V)
    [∀ i, DecidableEq (W.C i)]
    (comp : Completion W) (c : ∀ i, W.C i) : Prop :=
  ∃ i, ∃ c' : W.C i, ¬G.pref i (comp.complete c) (comp.complete (Function.update c i c'))

/-- Patchable is exactly the negation of IsProgramNash. -/
theorem isPatchable_iff_not_programNash (G : Game N V) (W : EvalWorld N V)
    [∀ i, DecidableEq (W.C i)]
    (comp : Completion W) (c : ∀ i, W.C i) :
    IsPatchable G W comp c ↔ ¬IsProgramNash G W comp c := by
  unfold IsPatchable IsProgramNash Game.IsPureNash completionGame
  simp only
  constructor
  · intro ⟨i, c', hc'⟩ hNash
    exact hc' (hNash i c')
  · intro hNotNash
    push_neg at hNotNash
    exact hNotNash

end SyntheticGameTheory
