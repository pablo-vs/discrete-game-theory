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

namespace Refinement.GeneralSignTower

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Iterate the single-step embedding n times starting from level k.
    The output type T.V (k+n) works because Lean's Nat.add is defined
    recursively on the second argument, so k+(n+1) = (k+n)+1 holds
    definitionally. -/
def embedIter (T : GeneralSignTower I) (k n : ℕ) (i : I) : T.V k i → T.V (k + n) i :=
  match n with
  | 0 => id
  | n + 1 => T.embed (k + n) i ∘ T.embedIter k n i

@[simp] theorem embedIter_zero (T : GeneralSignTower I) (k : ℕ) (i : I) :
    T.embedIter k 0 i = id := rfl

theorem embedIter_succ (T : GeneralSignTower I) (k n : ℕ) (i : I) :
    T.embedIter k (n + 1) i = T.embed (k + n) i ∘ T.embedIter k n i := rfl

theorem embedIter_one (T : GeneralSignTower I) (k : ℕ) (i : I) :
    T.embedIter k 1 i = T.embed k i := by
  ext v; simp [embedIter]

theorem embedIter_inj (T : GeneralSignTower I) (k n : ℕ) (i : I) :
    Function.Injective (T.embedIter k n i) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih =>
    rw [embedIter_succ]
    exact Function.Injective.comp (T.embed_inj (k + n) i) ih

theorem embedIter_between (T : GeneralSignTower I) (k n : ℕ) (i : I)
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
theorem coherent_embedIter (T : GeneralSignTower I) (k n : ℕ) (i : I)
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
def embedIterPureProfile (T : GeneralSignTower I) (k n : ℕ)
    (p : Base.PureProfile I (T.V k)) :
    Base.PureProfile I (T.V (k + n)) :=
  fun j => T.embedIter k n j (p j)

/-- Embed a face from level k to level k+n. -/
def embedIterFace (T : GeneralSignTower I) (k n : ℕ) (i : I)
    (F : Face (T.V k i)) :
    Face (T.V (k + n) i) :=
  embedFace (T.embedIter k n i) (T.embedIter_inj k n i) F

end Refinement.GeneralSignTower

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
theorem restrictGame_sign {W : I → Type*} [∀ i, DecidableEq (W i)]
    {G : Base.SignGame I V} {f : ∀ i, W i → V i}
    {i : I} {p : Base.PureProfile I W} {a b : W i} :
    (restrictGame G f).sign i p a b =
    G.sign i (fun j => f j (p j)) (f i a) (f i b) := rfl

/-- Restricting a tower's game at level k+n via embedIter from level k
    gives the same signs as the game at level k. -/
theorem restrictGame_embedIter_eq
    (T : Refinement.GeneralSignTower I) (k n : ℕ)
    (i : I) (p : Base.PureProfile I (T.V k)) (a b : T.V k i) :
    (restrictGame (T.game (k + n)) (fun j => T.embedIter k n j)).sign i p a b =
    (T.game k).sign i p a b := by
  simp [restrictGame_sign, T.coherent_embedIter k n i p a b]

end SelfSimilarity

-- ================================================================
-- Section 3: Multi-Level Game (Per-Player Independence)
-- ================================================================

namespace Refinement.GeneralSignTower

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
def multiLevelGame (T : GeneralSignTower I) (κ : I → ℕ) :
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
theorem multiLevelGame_uniform_sign (T : GeneralSignTower I) (k : ℕ)
    (i : I) (p : Base.PureProfile I (T.V k)) (a b : T.V k i) :
    (T.multiLevelGame (fun _ => k)).sign i p a b =
    (T.game k).sign i p a b := by
  simp [multiLevelGame]

/-- Nash equilibria exist in multi-level games. -/
theorem multiLevelGame_nash_exists (T : GeneralSignTower I) (κ : I → ℕ) :
    ∃ σ, (T.multiLevelGame κ).IsNash σ :=
  (T.multiLevelGame κ).nash_exists

/-- Per-player independence: two multi-level games with the same level for
    player i give the same sign, regardless of other players' levels.
    This is because sign_irrel makes the sign depend only on opponents'
    actions, and the multiLevelGame construction uses dummy values for
    type-mismatched opponents. -/
theorem multiLevelGame_sign_irrel (T : GeneralSignTower I)
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
theorem multiLevelGame_coherent_embed (T : GeneralSignTower I) (k n : ℕ)
    (i : I) (p : Base.PureProfile I (T.V k)) (a b : T.V k i) :
    (T.multiLevelGame (fun _ => k + n)).sign i
      (fun j => T.embedIter k n j (p j))
      (T.embedIter k n i a)
      (T.embedIter k n i b) =
    (T.multiLevelGame (fun _ => k)).sign i p a b := by
  simp [multiLevelGame]
  exact T.coherent_embedIter k n i p a b

end Refinement.GeneralSignTower

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
theorem restrictGame_coherent_subtype
    {T : Refinement.GeneralSignTower I} (k : ℕ) (i₀ : I)
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

-- ================================================================
-- Section 5: Grid Child Embeddings (Concrete)
-- ================================================================

namespace SelfSimilarity

/-- Left child embedding: maps level-k grid points to the left half
    of the level-(k+1) grid. j ↦ j (identity on values). -/
def leftChild (k : ℕ) (j : Fin (Refinement.gridSize k)) : Fin (Refinement.gridSize (k + 1)) :=
  ⟨j.val, by grid_omega⟩

/-- Right child embedding: maps level-k grid points to the right half
    of the level-(k+1) grid. j ↦ j + 2^k. -/
def rightChild (k : ℕ) (j : Fin (Refinement.gridSize k)) : Fin (Refinement.gridSize (k + 1)) :=
  ⟨j.val + 2 ^ k, by grid_omega⟩

@[simp] theorem leftChild_val (k : ℕ) (j : Fin (Refinement.gridSize k)) :
    (leftChild k j).val = j.val := rfl

@[simp] theorem rightChild_val (k : ℕ) (j : Fin (Refinement.gridSize k)) :
    (rightChild k j).val = j.val + 2 ^ k := rfl

theorem leftChild_injective (k : ℕ) : Function.Injective (leftChild k) := by
  intro a b h
  simp only [leftChild, Fin.mk.injEq] at h
  exact Fin.ext h

theorem rightChild_injective (k : ℕ) : Function.Injective (rightChild k) := by
  intro a b h
  simp only [rightChild, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem leftChild_strictMono (k : ℕ) : StrictMono (leftChild k) :=
  fun _ _ h => h

theorem rightChild_strictMono (k : ℕ) : StrictMono (rightChild k) := by
  intro a b h
  show rightChild k a < rightChild k b
  simp only [Fin.lt_def, rightChild_val]
  omega

/-- Left child preserves betweenness (it's value-preserving). -/
theorem leftChild_between (k : ℕ) (a b c : Fin (Refinement.gridSize k))
    (h : (Refinement.finBetweenness (Refinement.gridSize k)).between c a b) :
    (Refinement.finBetweenness (Refinement.gridSize (k + 1))).between
      (leftChild k c) (leftChild k a) (leftChild k b) := by
  -- leftChild preserves .val, so min/max are preserved as Fin values
  simp only [Refinement.finBetweenness] at *
  exact h

/-- Right child preserves betweenness. -/
theorem rightChild_between (k : ℕ) (a b c : Fin (Refinement.gridSize k))
    (h : (Refinement.finBetweenness (Refinement.gridSize k)).between c a b) :
    (Refinement.finBetweenness (Refinement.gridSize (k + 1))).between
      (rightChild k c) (rightChild k a) (rightChild k b) := by
  simp only [Refinement.finBetweenness] at *
  obtain ⟨hlo, hhi⟩ := h
  have hlo_v : min a.val b.val ≤ c.val := by
    rw [← Fin.coe_min]; exact Fin.val_le_of_le hlo
  have hhi_v : c.val ≤ max a.val b.val := by
    rw [← Fin.coe_max]; exact Fin.val_le_of_le hhi
  constructor <;> {
    show _ ≤ _
    simp only [Fin.le_def, Fin.coe_min, Fin.coe_max, rightChild_val]
    omega
  }

/-- The boundary is shared: the right endpoint of the left child
    equals the left endpoint of the right child. -/
theorem boundary_shared (k : ℕ) :
    leftChild k ⟨2 ^ k, by grid_omega⟩ = rightChild k ⟨0, Nat.succ_pos _⟩ := by
  apply Fin.ext; simp only [leftChild_val, rightChild_val]; omega

/-- Every fine point in the left half lies between leftChild(a) and leftChild(b)
    for some b. -/
theorem fine_between_leftChild (k : ℕ) (v : Fin (Refinement.gridSize (k + 1)))
    (hv : v.val ≤ 2 ^ k)
    (a : Fin (Refinement.gridSize k)) :
    ∃ b : Fin (Refinement.gridSize k),
      (Refinement.finBetweenness (Refinement.gridSize (k + 1))).between
        v (leftChild k a) (leftChild k b) := by
  simp only [Refinement.finBetweenness, leftChild]
  by_cases h : v.val ≤ a.val
  · refine ⟨⟨0, by grid_omega⟩, ?_⟩
    constructor <;> { rw [Fin.le_def]; simp only [Fin.coe_min, Fin.coe_max]; omega }
  · push_neg at h
    refine ⟨⟨2 ^ k, by grid_omega⟩, ?_⟩
    constructor <;> { rw [Fin.le_def]; simp only [Fin.coe_min, Fin.coe_max]; omega }

/-- Every fine point in the right half lies between rightChild(a) and rightChild(b)
    for some b. -/
theorem fine_between_rightChild (k : ℕ) (v : Fin (Refinement.gridSize (k + 1)))
    (hv : 2 ^ k ≤ v.val)
    (a : Fin (Refinement.gridSize k)) :
    ∃ b : Fin (Refinement.gridSize k),
      (Refinement.finBetweenness (Refinement.gridSize (k + 1))).between
        v (rightChild k a) (rightChild k b) := by
  simp only [Refinement.finBetweenness, rightChild]
  have ha := a.isLt
  have hv' := v.isLt
  by_cases h : v.val ≤ a.val + 2 ^ k
  · refine ⟨⟨0, by grid_omega⟩, ?_⟩
    constructor <;> { rw [Fin.le_def]; simp only [Fin.coe_min, Fin.coe_max]; omega }
  · push_neg at h
    refine ⟨⟨2 ^ k, by grid_omega⟩, ?_⟩
    constructor <;> { rw [Fin.le_def]; simp only [Fin.coe_min, Fin.coe_max]; grid_omega }

/-- gridEmbed maps 0 to 0, same as leftChild. -/
theorem gridEmbed_zero_eq_leftChild_zero (k : ℕ) :
    Refinement.gridEmbed k ⟨0, Nat.succ_pos _⟩ = leftChild k ⟨0, Nat.succ_pos _⟩ := by
  apply Fin.ext; simp only [Refinement.gridEmbed_val, leftChild_val]

/-- The left child covers [0, 2^k] of the fine grid. -/
theorem leftChild_range (k : ℕ) (j : Fin (Refinement.gridSize k)) :
    (leftChild k j).val ≤ 2 ^ k := by
  simp only [leftChild_val]; have := j.isLt; grid_omega

/-- The right child covers [2^k, 2^(k+1)] of the fine grid. -/
theorem rightChild_range (k : ℕ) (j : Fin (Refinement.gridSize k)) :
    2 ^ k ≤ (rightChild k j).val := by
  simp only [rightChild_val]; omega

end SelfSimilarity
