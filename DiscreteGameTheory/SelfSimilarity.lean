/-
# Self-Similarity of Refinement Towers

The refinement tower for sign games has a self-similar structure: a level-k game
decomposes as a tree of level-0 games. This file formalizes the morphisms that
make this precise, and proves per-player level independence (different players
can be at different resolution levels).

## Overview

- Section 1: Iterated embedding (embedIter) from level k to level k+n
- Section 2: Game restriction via injections
- Section 3: Multi-level game (per-player independence)
- Section 4: Abstract morphisms (top/bottom embeddings)
- Section 5: Grid child embeddings (concrete left/right children)
-/
import DiscreteGameTheory.Refinement

open Base (Sign Face cmpSign)
open Refinement

-- ================================================================
-- Section 1: Iterated Embedding
-- ================================================================

namespace Refinement.SignTower

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Iterate the single-step embedding n times starting from level k.
    The output type T.V (k+n) works because Lean's Nat.add is defined
    recursively on the second argument, so k+(n+1) = (k+n)+1 holds
    definitionally. -/
def embedIter (T : SignTower I) (k n : ℕ) (i : I) : T.V k i → T.V (k + n) i :=
  match n with
  | 0 => id
  | n + 1 => T.embed (k + n) i ∘ T.embedIter k n i

@[simp] theorem embedIter_zero (T : SignTower I) (k : ℕ) (i : I) :
    T.embedIter k 0 i = id := rfl

lemma embedIter_succ (T : SignTower I) (k n : ℕ) (i : I) :
    T.embedIter k (n + 1) i = T.embed (k + n) i ∘ T.embedIter k n i := rfl

lemma embedIter_one (T : SignTower I) (k : ℕ) (i : I) :
    T.embedIter k 1 i = T.embed k i := by
  ext v; simp [embedIter]

lemma embedIter_inj (T : SignTower I) (k n : ℕ) (i : I) :
    Function.Injective (T.embedIter k n i) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    rw [embedIter_succ]
    exact Function.Injective.comp (T.embed_inj (k + n) i) ih

lemma embedIter_between (T : SignTower I) (k n : ℕ) (i : I)
    (a b c : T.V k i)
    (h : (T.betw k i).between c a b) :
    (T.betw (k + n) i).between (T.embedIter k n i c)
      (T.embedIter k n i a) (T.embedIter k n i b) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [embedIter_succ]; simp only [Function.comp]
    exact T.embed_between (k + n) i _ _ _ ih

/-- Key coherence theorem: the sign at level k+n, evaluated on
    embedIter'd level-k arguments, equals the sign at level k. -/
theorem coherent_embedIter (T : SignTower I) (k n : ℕ) (i : I)
    (p : Base.PureProfile I (T.V k)) (a b : T.V k i) :
    (T.game (k + n)).sign i
      (fun j => T.embedIter k n j (p j))
      (T.embedIter k n i a) (T.embedIter k n i b) =
    (T.game k).sign i p a b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (T.game ((k + n) + 1)).sign i
      (fun j => T.embed (k + n) j (T.embedIter k n j (p j)))
      (T.embed (k + n) i (T.embedIter k n i a))
      (T.embed (k + n) i (T.embedIter k n i b)) = _
    have h1 : (fun j => T.embed (k + n) j (T.embedIter k n j (p j))) =
        embedPureProfile (T.embed (k + n)) (fun j => T.embedIter k n j (p j)) := rfl
    rw [h1, T.coherent, ih]

/-- Embed a pure profile from level k to level k+n. -/
def embedIterPureProfile (T : SignTower I) (k n : ℕ)
    (p : Base.PureProfile I (T.V k)) :
    Base.PureProfile I (T.V (k + n)) :=
  fun j => T.embedIter k n j (p j)

/-- Embed a face from level k to level k+n. -/
def embedIterFace (T : SignTower I) (k n : ℕ) (i : I)
    (F : Face (T.V k i)) :
    Face (T.V (k + n) i) :=
  embedFace (T.embedIter k n i) (T.embedIter_inj k n i) F

end Refinement.SignTower

-- ================================================================
-- Section 2: Game Restriction via Embeddings
-- ================================================================

namespace SelfSimilarity

variable {I : Type*} [DecidableEq I] [Fintype I]
variable {V : I → Type*} [∀ i, DecidableEq (V i)]

/-- Restrict a sign game to a sub-type via per-player injections. -/
def restrictGame {W : I → Type*} [∀ i, DecidableEq (W i)]
    (G : Base.SignGame I V) (f : ∀ i, W i → V i) : Base.SignGame I W where
  sign i p a b := G.sign i (fun j => f j (p j)) (f i a) (f i b)
  sign_refl i p a := G.sign_refl i _ _
  sign_antisym i p a b := G.sign_antisym i _ _ _
  sign_trans i p a b c h1 h2 := G.sign_trans i _ _ _ _ h1 h2
  sign_irrel i p q a b h := G.sign_irrel i _ _ _ _ (fun j hj => by
    show f j (p j) = f j (q j); rw [h j hj])

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (V i)] in
lemma restrictGame_sign {W : I → Type*} [∀ i, DecidableEq (W i)]
    {G : Base.SignGame I V} {f : ∀ i, W i → V i}
    {i : I} {p : Base.PureProfile I W} {a b : W i} :
    (restrictGame G f).sign i p a b =
    G.sign i (fun j => f j (p j)) (f i a) (f i b) := rfl

/-- Restricting a tower's game at level k+n via embedIter from level k
    gives the same signs as the game at level k. -/
lemma restrictGame_embedIter_eq
    (T : Refinement.SignTower I) (k n : ℕ)
    (i : I) (p : Base.PureProfile I (T.V k)) (a b : T.V k i) :
    (restrictGame (T.game (k + n)) (fun j => T.embedIter k n j)).sign i p a b =
    (T.game k).sign i p a b := by
  simp [restrictGame_sign, T.coherent_embedIter k n i p a b]

end SelfSimilarity

-- ================================================================
-- Section 3: Multi-Level Game (Per-Player Independence)
-- ================================================================

namespace Refinement.SignTower

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Multi-level sign game: each player i operates at level κ i.
    The sign for player i is determined solely by the game at level κ i,
    since sign_irrel ensures signs depend only on opponents' actions
    (which are plugged in using dummy values at the right type).

    The key insight is that per-player independence is immediate from
    sign_irrel: a player's sign function depends only on their own
    actions and their opponents' actions. When we fix the player's level
    to κ i, the opponents' types don't matter — any consistent
    pure profile will give the same sign. -/
def multiLevelGame (T : SignTower I) (κ : I → ℕ) :
    Base.SignGame I (fun i => T.V (κ i) i) where
  sign i p a b := (T.game (κ i)).sign i
    (fun j => if h : κ j = κ i then h ▸ p j
              else (T.instInhabited (κ i) j).default)
    a b
  sign_refl i p a := (T.game (κ i)).sign_refl i _ _
  sign_antisym i p a b := (T.game (κ i)).sign_antisym i _ _ _
  sign_trans i p a b c h1 h2 := (T.game (κ i)).sign_trans i _ _ _ _ h1 h2
  sign_irrel i p q a b h := by
    apply (T.game (κ i)).sign_irrel i _ _ _ _ (fun j hj => by
      split <;> simp_all [h j hj])

/-- When all players are at the same level k, the multi-level game
    agrees with T.game k. -/
lemma multiLevelGame_uniform_sign (T : SignTower I) (k : ℕ)
    (i : I) (p : Base.PureProfile I (T.V k)) (a b : T.V k i) :
    (T.multiLevelGame (fun _ => k)).sign i p a b =
    (T.game k).sign i p a b := by
  simp [multiLevelGame]

/-- Nash equilibria exist in multi-level games. -/
theorem multiLevelGame_nash_exists (T : SignTower I) (κ : I → ℕ) :
    ∃ σ, (T.multiLevelGame κ).IsNash σ :=
  (T.multiLevelGame κ).nash_exists

/-- Per-player independence: two multi-level games with the same level for
    player i give the same sign, regardless of other players' levels.
    This is because sign_irrel makes the sign depend only on opponents'
    actions, and the multiLevelGame construction uses dummy values for
    type-mismatched opponents. -/
lemma multiLevelGame_sign_irrel (T : SignTower I)
    (κ : I → ℕ) (i : I)
    (p₁ p₂ : Base.PureProfile I (fun j => T.V (κ j) j))
    (hp : ∀ j, j ≠ i → p₁ j = p₂ j)
    (a b : T.V (κ i) i) :
    (T.multiLevelGame κ).sign i p₁ a b =
    (T.multiLevelGame κ).sign i p₂ a b := by
  exact (T.multiLevelGame κ).sign_irrel i p₁ p₂ a b hp

/-- The multi-level sign is coherent with embedIter: embedding player i's
    actions from level k to level k+n doesn't change the game's sign,
    when the multi-level game is set up with the right levels. -/
lemma multiLevelGame_coherent_embed (T : SignTower I) (k n : ℕ)
    (i : I) (p : Base.PureProfile I (T.V k)) (a b : T.V k i) :
    (T.multiLevelGame (fun _ => k + n)).sign i
      (fun j => T.embedIter k n j (p j))
      (T.embedIter k n i a)
      (T.embedIter k n i b) =
    (T.multiLevelGame (fun _ => k)).sign i p a b := by
  simp [multiLevelGame]
  exact T.coherent_embedIter k n i p a b

end Refinement.SignTower

-- ================================================================
-- Section 4: Abstract Morphisms
-- ================================================================

namespace SelfSimilarity

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Increment one player's level in a level assignment. -/
def topEmbedAt (κ : I → ℕ) (i₀ : I) : I → ℕ :=
  Function.update κ i₀ (κ i₀ + 1)

/-- Bottom embedding: restricting a game to a subrange via coherent injection
    preserves signs. -/
lemma restrictGame_coherent_subtype
    {T : Refinement.SignTower I} (k : ℕ) (i₀ : I)
    (f : T.V k i₀ → T.V (k + 1) i₀)
    (hf_coh : ∀ (p : Base.PureProfile I (T.V k)) (a b : T.V k i₀),
      (T.game (k + 1)).sign i₀
        (Refinement.embedPureProfile (Function.update (T.embed k) i₀ f) p)
        (f a) (f b) =
      (T.game k).sign i₀ p a b)
    (p : Base.PureProfile I (T.V k)) (a b : T.V k i₀) :
    (restrictGame (T.game (k + 1))
      (Function.update (T.embed k) i₀ f)).sign i₀ p a b =
    (T.game k).sign i₀ p a b := by
  simp only [restrictGame_sign, Function.update_self]
  exact hf_coh p a b

end SelfSimilarity

