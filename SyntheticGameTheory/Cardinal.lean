import SyntheticGameTheory
import SyntheticGameTheory.DyadicGrid
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity

/-!
# Cardinal Games and the Synthetic VNM Theorem

The ordinal proof (`nash_exists`) finds a Nash *face* — a set of pure
actions per player from which no player can profitably deviate. This is
the entire game-theoretic content.

Locating the exact equilibrium *mixture* within the face is not game
theory — it is coordinate specification. Given integer-valued cardinal
utilities consistent with the ordinal preferences, the equilibrium
mixing weights are determined by a system of linear inequalities with
integer coefficients. At dyadic precision k, we discretize the mixture
simplex into a grid and ask: is there a grid point satisfying these
inequalities? The answer is yes, by applying `nash_exists` to the
grid game.

The key structural result (`gridGame_pref_pureGrid`) shows that the
grid game's preferences on pure vertex embeddings exactly match the
original ordinal preferences. So the grid game is a faithful cardinal
refinement — it adds precision without changing the game theory.

Informally: iterating this at increasing precision k = 0, 1, 2, ...
produces a sequence of dyadic approximations converging to a computable
real-valued equilibrium. We do not formalize convergence (it requires
analysis over ℝ), but the existence at each finite precision is the
content that matters.
-/

namespace SyntheticGameTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]

-- ================================================================
-- Section 1: Cardinal Games
-- ================================================================

/-- A cardinal game extends an ordinal game with integer-valued utilities
    consistent with the ordinal preferences. The integers represent one
    level of precision — different assignments inducing the same ordinal
    order are equivalent. -/
structure CardinalGame (N : Type*) [DecidableEq N] [Fintype N]
    (V : N → Type*) [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)]
    extends Game N V where
  util : N → PureProfile N V → ℤ
  util_pref : ∀ i p q, pref i p q ↔ util i q ≤ util i p

-- ================================================================
-- Section 2: Pure Embedding into the Grid
-- ================================================================

/-- Embed a vertex as a grid action concentrating all weight on it. -/
def vertexGrid {W : Type*} [DecidableEq W] (v : W) (k : ℕ) : GridAction W k :=
  fun w => if w = v then ⟨2^k, by omega⟩ else 0

/-- Embed a pure profile as a grid profile. -/
def pureGrid (p : PureProfile N V) (k : ℕ) : GridProfile N V k :=
  fun i => vertexGrid (p i) k

@[simp]
theorem vertexGrid_val {W : Type*} [DecidableEq W] (v w : W) (k : ℕ) :
    (vertexGrid v k w).val = if w = v then 2^k else 0 := by
  simp only [vertexGrid]; split_ifs <;> simp

omit [DecidableEq N] in
/-- The weight product for pure embeddings: nonzero only when the profiles
    match, in which case it equals (2^k)^|N|. -/
theorem pureGrid_prod (p q : PureProfile N V) (k : ℕ) :
    (Finset.univ.prod fun j : N => ((pureGrid p k j (q j)).val : ℤ)) =
    if q = p then ((2^k : ℕ) : ℤ) ^ Fintype.card N else 0 := by
  classical
  simp only [pureGrid, vertexGrid_val]
  by_cases h : q = p
  · subst h; simp [Finset.prod_const, Finset.card_univ]
  · have ⟨j, hj⟩ : ∃ j, q j ≠ p j := by
      by_contra h'; push_neg at h'; exact h (funext h')
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

-- ================================================================
-- Section 3: Grid Utility and the Grid Game
-- ================================================================

namespace CardinalGame

variable (G : CardinalGame N V)

/-- Expected utility of player i under a grid profile: the weighted sum
    over all pure profiles, where each profile's weight is the product of
    the per-player grid weights on its actions. -/
noncomputable def gridUtil (k : ℕ) (i : N) (σ : GridProfile N V k) : ℤ :=
  Finset.univ.sum fun p : PureProfile N V =>
    (Finset.univ.prod fun j : N => ((σ j (p j)).val : ℤ)) * G.util i p

/-- The grid game at precision k. Players choose grid actions (dyadic weight
    vectors); preferences are determined by grid utility. -/
noncomputable def gridGame (k : ℕ) : Game N (fun i => GridAction (V i) k) where
  pref i σ σ' := G.gridUtil k i σ' ≤ G.gridUtil k i σ
  pref_preorder _ := {
    refl := fun _ => le_refl _
    trans := fun _ _ _ h1 h2 => le_trans h2 h1
  }
  pref_total _ :=
    ⟨fun _ _ => le_total _ _⟩
  pref_decidable _ _ _ := Int.decLe _ _

-- ================================================================
-- Section 4: Preference Preservation
-- ================================================================

/-- Grid utility on pure embeddings equals a positive scaling factor times
    the original utility. -/
theorem gridUtil_pureGrid (i : N) (p : PureProfile N V) (k : ℕ) :
    G.gridUtil k i (pureGrid p k) =
    ((2^k : ℕ) : ℤ) ^ Fintype.card N * G.util i p := by
  simp only [gridUtil, pureGrid_prod, ite_mul, zero_mul]; simp

omit [DecidableEq N] in
private lemma scaling_pos (k : ℕ) :
    (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) ^ Fintype.card N := by positivity

/-- **Preference preservation**: the grid game's preferences on pure
    vertex embeddings exactly match the original ordinal preferences.
    The grid game is a faithful cardinal refinement of the ordinal game. -/
theorem gridGame_pref_pureGrid (i : N) (p q : PureProfile N V) (k : ℕ) :
    (gridGame G k).pref i (pureGrid p k) (pureGrid q k) ↔
    G.toGame.pref i p q := by
  show G.gridUtil k i (pureGrid q k) ≤ G.gridUtil k i (pureGrid p k) ↔ _
  rw [gridUtil_pureGrid, gridUtil_pureGrid, G.util_pref]
  exact Int.mul_le_mul_left (scaling_pos k)

-- ================================================================
-- Section 5: Nash Existence at Every Precision
-- ================================================================

/-- **Synthetic VNM theorem**: at every dyadic precision k, the grid game
    has a Nash equilibrium. Combined with the ordinal `nash_exists`, this
    says: the ordinal proof finds the game-theoretic structure (which
    vertices are in the equilibrium support), and the cardinal grid game
    finds the mixing weights to k bits of precision.

    Iterating over k = 0, 1, 2, ... yields a sequence of increasingly
    precise dyadic equilibrium approximations. -/
theorem grid_nash_exists [∀ i, Nonempty (V i)] (k : ℕ) :
    ∃ σ, (gridGame G k).IsNash σ :=
  (gridGame G k).nash_exists

end CardinalGame

end SyntheticGameTheory
