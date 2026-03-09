/-
# General Refinement Tower for N-Player Sign Games

Builds on Base.lean to show that Nash equilibria at level k can be
refined to level k+1, for arbitrary numbers of players and actions.

## Overview

Layer A: Betweenness and convex closure on abstract grids
Layer B: GeneralSignTower structure with embedding and convexity axioms
Layer C: Transfer theorems (DevFaceLE under closure, OD transfer)
Layer D: Nash refinement sequence
-/
import SyntheticGameTheory.Base

namespace Refinement

open Base (Sign Face cmpSign)
open Base.SignGame (DevFaceLE OutsideDominated)

-- ================================================================
-- Layer A: Betweenness and Convex Closure
-- ================================================================

/-- A betweenness relation on a type. `between c a b` means c lies
    on the segment from a to b in the grid. -/
class Betweenness (V : Type*) where
  between : V → V → V → Prop
  between_refl_left : ∀ a b, between a a b
  between_refl_right : ∀ a b, between b a b
  between_symm : ∀ a b c, between c a b → between c b a
  between_self : ∀ a c, between c a a → c = a
  between_dec : ∀ c a b, Decidable (between c a b)

attribute [instance] Betweenness.between_dec

section ConvexClosure

variable {V : Type*} [DecidableEq V] [Fintype V] [Betweenness V]

/-- A finset is convex if closed under betweenness. -/
def IsConvex (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c, Betweenness.between c a b → c ∈ S

/-- Decidability of IsConvex, needed for computable convClosure. -/
instance IsConvex.decidable (S : Finset V) : Decidable (IsConvex S) :=
  inferInstanceAs (Decidable (∀ a ∈ S, ∀ b ∈ S, ∀ c, Betweenness.between c a b → c ∈ S))

/-- The convex closure: smallest convex superset.
    Defined as the intersection of all convex supersets within Finset.univ. -/
def convClosure (F : Face V) : Face V :=
  ⟨Finset.univ.filter (fun v => ∀ S : Finset V, F.val ⊆ S → IsConvex S → v ∈ S),
   let ⟨x, hx⟩ := F.property
   ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, fun S hFS _ => hFS hx⟩⟩⟩

-- ----------------------------------------------------------------
-- Convex closure API
-- ----------------------------------------------------------------

theorem mem_convClosure (F : Face V) (v : V) :
    v ∈ (convClosure F).val ↔ ∀ S : Finset V, F.val ⊆ S → IsConvex S → v ∈ S := by
  simp [convClosure, Finset.mem_filter]

/-- F ⊆ convClosure F. -/
theorem face_sub_closure (F : Face V) :
    Face.IsSubface F (convClosure F) :=
  fun _ hv => (mem_convClosure F _).mpr (fun _ hFS _ => hFS hv)

/-- Universal property: convClosure F ⊆ S for any convex S ⊇ F. -/
theorem convClosure_sub_of_convex (F : Face V) (S : Finset V)
    (hFS : F.val ⊆ S) (hS : IsConvex S) :
    (convClosure F).val ⊆ S :=
  fun _ hv => (mem_convClosure F _).mp hv S hFS hS

/-- The convex closure is itself convex. -/
theorem IsConvex_convClosure (F : Face V) :
    IsConvex (convClosure F).val := by
  intro a ha b hb c hc
  rw [mem_convClosure] at ha hb ⊢
  intro S hFS hS
  exact hS a (ha S hFS hS) b (hb S hFS hS) c hc

/-- Convex closure is idempotent. -/
theorem convClosure_idempotent (F : Face V) :
    convClosure (convClosure F) = convClosure F := by
  apply Face.ext; ext v
  constructor
  · intro hv
    exact convClosure_sub_of_convex (convClosure F) (convClosure F).val
      (fun x hx => hx) (IsConvex_convClosure F) hv
  · intro hv
    exact face_sub_closure (convClosure F) hv

/-- Convex closure is monotone. -/
theorem convClosure_mono {F G : Face V}
    (h : Face.IsSubface F G) :
    Face.IsSubface (convClosure F) (convClosure G) := by
  intro v hv
  rw [mem_convClosure] at hv ⊢
  intro S hGS hS
  exact hv S (fun x hx => hGS (h hx)) hS

/-- Already-convex faces are fixed by convex closure. -/
theorem convClosure_of_convex {F : Face V}
    (h : IsConvex F.val) :
    convClosure F = F := by
  apply Face.ext; ext v
  constructor
  · intro hv; exact convClosure_sub_of_convex F F.val (fun x hx => hx) h hv
  · intro hv; exact face_sub_closure F hv

end ConvexClosure

-- ================================================================
-- Layer A.5: Fin-grid betweenness and grid arithmetic
-- ================================================================

/-- Natural-order betweenness on Fin n: c is between a and b iff
    min(a,b) ≤ c ≤ max(a,b). -/
instance finBetweenness (n : ℕ) : Betweenness (Fin n) where
  between c a b := min a b ≤ c ∧ c ≤ max a b
  between_refl_left a b := ⟨min_le_left a b, le_max_left a b⟩
  between_refl_right a b := ⟨min_le_right a b, le_max_right a b⟩
  between_symm a b c h := ⟨min_comm a b ▸ h.1, max_comm a b ▸ h.2⟩
  between_self a c h := le_antisymm (le_trans h.2 (max_le (le_refl a) (le_refl a)))
    (le_trans (le_min (le_refl a) (le_refl a)) h.1)
  between_dec _ _ _ := inferInstance

section FinGrid

/-- Grid size at level k: 2^k + 1 points discretizing [0,1]. -/
abbrev gridSize (k : ℕ) : ℕ := 2 ^ k + 1

/-- Number of edges (intervals) at level k: 2^k. -/
abbrev edgeCount (k : ℕ) : ℕ := 2 ^ k

-- omega can't handle 2^k. This unfolds pow_succ and lets omega finish.
macro "grid_omega" : tactic =>
  `(tactic| (simp only [gridSize, edgeCount, Nat.pow_succ, Nat.mul_comm] at *; omega))

/-- Embed level-k grid point into level-(k+1) grid: j ↦ 2j. -/
def gridEmbed (k : ℕ) (j : Fin (gridSize k)) : Fin (gridSize (k + 1)) :=
  ⟨2 * j.val, by grid_omega⟩

theorem gridEmbed_injective (k : ℕ) : Function.Injective (gridEmbed k) := by
  intro a b h; simp [gridEmbed, Fin.ext_iff] at h; exact Fin.ext (by omega)

@[simp] theorem gridEmbed_val (k : ℕ) (j : Fin (gridSize k)) :
    (gridEmbed k j).val = 2 * j.val := rfl

/-- Midpoint between embedded grid points 2j and 2(j+1): maps to 2j+1. -/
def gridMidpoint (k : ℕ) (j : Fin (edgeCount k)) : Fin (gridSize (k + 1)) :=
  ⟨2 * j.val + 1, by grid_omega⟩

@[simp] theorem gridMidpoint_val (k : ℕ) (j : Fin (edgeCount k)) :
    (gridMidpoint k j).val = 2 * j.val + 1 := rfl

/-- Right endpoint of a coarse edge embedded into the fine grid. -/
def gridEmbedRight (k : ℕ) (j : Fin (edgeCount k)) : Fin (gridSize (k + 1)) :=
  gridEmbed k ⟨j.val + 1, by grid_omega⟩

@[simp] theorem gridEmbedRight_val (k : ℕ) (j : Fin (edgeCount k)) :
    (gridEmbedRight k j).val = 2 * j.val + 2 := by
  simp [gridEmbedRight, gridEmbed_val]; omega

/-- gridEmbed preserves betweenness. -/
theorem gridEmbed_between (k : ℕ) (a b c : Fin (gridSize k))
    (h : (finBetweenness (gridSize k)).between c a b) :
    (finBetweenness (gridSize (k+1))).between (gridEmbed k c) (gridEmbed k a) (gridEmbed k b) := by
  simp only [finBetweenness] at *
  obtain ⟨hlo, hhi⟩ := h
  have hlo_v : min a.val b.val ≤ c.val := by
    rw [← Fin.coe_min]; exact Fin.val_le_of_le hlo
  have hhi_v : c.val ≤ max a.val b.val := by
    rw [← Fin.coe_max]; exact Fin.val_le_of_le hhi
  constructor <;> {
    rw [Fin.le_def]
    simp only [Fin.coe_min, Fin.coe_max, gridEmbed_val]
    omega
  }

/-- Every fine grid point v lies between embed(a) and embed(b) for some b. -/
theorem fine_between_gridEmbed (k : ℕ) (v : Fin (gridSize (k+1))) (a : Fin (gridSize k)) :
    ∃ b : Fin (gridSize k),
      (finBetweenness (gridSize (k+1))).between v (gridEmbed k a) (gridEmbed k b) := by
  simp only [finBetweenness]
  by_cases h : v.val ≤ 2 * a.val
  · refine ⟨⟨0, by grid_omega⟩, ?_⟩
    constructor <;> {
      rw [Fin.le_def]
      simp only [Fin.coe_min, Fin.coe_max, gridEmbed_val]
      omega
    }
  · push_neg at h
    refine ⟨⟨gridSize k - 1, by grid_omega⟩, ?_⟩
    constructor <;> {
      rw [Fin.le_def]
      simp only [Fin.coe_min, Fin.coe_max, gridEmbed_val]
      have := v.isLt
      grid_omega
    }

instance gridSize_inhabited (k : ℕ) : Inhabited (Fin (gridSize k)) :=
  ⟨⟨0, Nat.succ_pos _⟩⟩

instance gridSize_nonempty (k : ℕ) : Nonempty (Fin (gridSize k)) := ⟨default⟩

end FinGrid

-- ================================================================
-- Layer B: General Sign Tower
-- ================================================================

-- ----------------------------------------------------------------
-- Embedding infrastructure
-- ----------------------------------------------------------------

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Embed a pure profile from level k to level k+1. -/
def embedPureProfile {V₀ V₁ : I → Type*}
    (emb : ∀ i, V₀ i → V₁ i) (p : Base.PureProfile I V₀) :
    Base.PureProfile I V₁ :=
  fun i => emb i (p i)

/-- Embed a face from one type to another. -/
def embedFace {W₀ W₁ : Type*} [DecidableEq W₀] [DecidableEq W₁]
    (emb_i : W₀ → W₁) (emb_inj : Function.Injective emb_i)
    (F : Face W₀) : Face W₁ :=
  ⟨F.val.map ⟨emb_i, emb_inj⟩,
   let ⟨x, hx⟩ := F.property; ⟨emb_i x, Finset.mem_map_of_mem _ hx⟩⟩

/-- Embed a profile (all players' faces). -/
def embedProfile {V₀ V₁ : I → Type*}
    [∀ i, DecidableEq (V₀ i)] [∀ i, DecidableEq (V₁ i)]
    (emb : ∀ i, V₀ i → V₁ i)
    (emb_inj : ∀ i, Function.Injective (emb i))
    (σ : Base.Profile I V₀) : Base.Profile I V₁ :=
  fun i => embedFace (emb i) (emb_inj i) (σ i)

-- ----------------------------------------------------------------
-- The tower structure
-- ----------------------------------------------------------------

/-- A tower of N-player sign games at increasing precision levels. -/
structure GeneralSignTower (I : Type*) [DecidableEq I] [Fintype I] where
  /-- Action types at each level, per player -/
  V : ℕ → I → Type*
  instDecEq : ∀ k i, DecidableEq (V k i)
  instFintype : ∀ k i, Fintype (V k i)
  instInhabited : ∀ k i, Inhabited (V k i)
  betw : ∀ k i, Betweenness (V k i)
  game : (k : ℕ) → Base.SignGame I (V k)
  embed : ∀ k i, V k i → V (k+1) i
  embed_inj : ∀ k i, Function.Injective (embed k i)
  embed_between : ∀ k i (a b c : V k i),
    (betw k i).between c a b →
    (betw (k+1) i).between (embed k i c) (embed k i a) (embed k i b)
  coherent : ∀ k i (p : Base.PureProfile I (V k)) (a b : V k i),
    (game (k+1)).sign i (embedPureProfile (embed k) p) (embed k i a) (embed k i b)
    = (game k).sign i p a b
  playerConvex_left : ∀ k i (p : Base.PureProfile I (V k))
    (a b c x : V k i),
    (betw k i).between c a b →
    ((game k).sign i p a x).nonneg →
    ((game k).sign i p b x).nonneg →
    ((game k).sign i p c x).nonneg
  playerConvex_right : ∀ k i (p : Base.PureProfile I (V k))
    (a b c x : V k i),
    (betw k i).between c a b →
    ((game k).sign i p x a).nonneg →
    ((game k).sign i p x b).nonneg →
    ((game k).sign i p x c).nonneg
  opponentConvex : ∀ k i (j : I) (_hj : j ≠ i)
    (p q : Base.PureProfile I (V k)) (a b : V k i),
    (∀ m, m ≠ j → p m = q m) →
    ∀ (r : Base.PureProfile I (V k)),
    (∀ m, m ≠ j → r m = p m) →
    (betw k j).between (r j) (p j) (q j) →
    ((game k).sign i p a b).nonneg →
    ((game k).sign i q a b).nonneg →
    ((game k).sign i r a b).nonneg
  /-- Every fine action lies between the embedding of any given coarse action
      and the embedding of some other coarse action. This ensures the embedded
      coarse grid "spans" the fine grid from every anchor point.
      Needed for OD transfer at non-embedded outside points (Patch 8). -/
  fine_between_embedded_at : ∀ k i (v : V (k+1) i) (a : V k i),
    ∃ b : V k i, (betw (k+1) i).between v (embed k i a) (embed k i b)

namespace GeneralSignTower

variable {I : Type*} [DecidableEq I] [Fintype I]
variable (T : GeneralSignTower I)

-- Provide instances from the tower
instance instDE (k : ℕ) (i : I) : DecidableEq (T.V k i) := T.instDecEq k i
instance instFT (k : ℕ) (i : I) : Fintype (T.V k i) := T.instFintype k i
instance instInh (k : ℕ) (i : I) : Inhabited (T.V k i) := T.instInhabited k i
instance instNE (k : ℕ) (i : I) : Nonempty (T.V k i) := ⟨default⟩
instance instBW (k : ℕ) (i : I) : Betweenness (T.V k i) := T.betw k i

-- ----------------------------------------------------------------
-- Convex closure for profiles (close each player's face)
-- ----------------------------------------------------------------

def convCloseProfile (k : ℕ)
    (σ : Base.Profile I (T.V k)) :
    Base.Profile I (T.V k) :=
  fun i => @convClosure (T.V k i) (T.instDecEq k i) (T.instFintype k i)
    (T.betw k i) (σ i)

-- Helper: abbreviation for convClosure at a specific tower level/player
def cc (k : ℕ) (i : I) (F : Face (T.V k i)) : Face (T.V k i) :=
  @convClosure (T.V k i) (T.instDecEq k i) (T.instFintype k i) (T.betw k i) F

-- ================================================================
-- Layer C: Transfer Theorems
-- ================================================================

-- ----------------------------------------------------------------
-- C.0: Helper lemmas
-- ----------------------------------------------------------------

/-- DevFaceLE is insensitive to player i's own face in the profile,
    since consistency only checks opponents j ≠ i. -/
theorem DevFaceLE_update_self (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {F : Face (T.V k i)}
    {A B : Face (T.V k i)} :
    (T.game k).DevFaceLE i (Function.update σ i F) A B ↔
    (T.game k).DevFaceLE i σ A B := by
  constructor
  · intro h a ha p hp b hb
    exact h a ha p (fun m hm => by
      rw [Function.update_of_ne hm]; exact hp m hm) b hb
  · intro h a ha p hp b hb
    exact h a ha p (fun m hm => by
      have := hp m hm; rw [Function.update_of_ne hm] at this; exact this) b hb

/-- If v is between embed(w₀) and embed(b), w₀ ∈ F, and v ∉ cc(embed(F)),
    then b ∉ F. (If b ∈ F, both endpoints are inside cc, so v ∈ cc by
    convexity, contradicting the hypothesis.) -/
theorem outside_betw_witness_outside (k : ℕ) (i : I)
    (F : Face (T.V k i)) (w₀ : T.V k i) (hw₀ : w₀ ∈ F.val)
    (v : T.V (k+1) i)
    (hv : v ∉ (T.cc (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) F)).val)
    (b : T.V k i)
    (hbetw : (T.betw (k+1) i).between v (T.embed k i w₀) (T.embed k i b)) :
    b ∉ F.val := by
  intro hb
  apply hv
  set ccF := T.cc (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) F)
  exact IsConvex_convClosure _ _ (face_sub_closure _ (Finset.mem_map_of_mem _ hw₀))
    _ (face_sub_closure _ (Finset.mem_map_of_mem _ hb)) v hbetw

-- ----------------------------------------------------------------
-- C.1: DevFaceLE preserved under convex closure of player faces
-- ----------------------------------------------------------------

/-- DevFaceLE preserved under convex closure of the left (player) face. -/
theorem DevFaceLE_convClosure_left (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).DevFaceLE i σ A B) :
    (T.game k).DevFaceLE i σ (T.cc k i A) B := by
  intro a ha p hp b hb
  set S := Finset.univ.filter (fun v => ((T.game k).sign i p v b).nonneg)
  have hAS : A.val ⊆ S := fun v hv =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h v hv p hp b hb⟩
  have hSconv : @IsConvex _ (T.betw k i) S := fun v₁ hv₁ v₂ hv₂ c hc =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.playerConvex_left k i p v₁ v₂ c b hc
      (Finset.mem_filter.mp hv₁).2 (Finset.mem_filter.mp hv₂).2⟩
  exact (Finset.mem_filter.mp (convClosure_sub_of_convex A S hAS hSconv ha)).2

/-- DevFaceLE preserved under convex closure of the right (player) face. -/
theorem DevFaceLE_convClosure_right (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).DevFaceLE i σ A B) :
    (T.game k).DevFaceLE i σ A (T.cc k i B) := by
  intro a ha p hp b hb
  set S := Finset.univ.filter (fun v => ((T.game k).sign i p a v).nonneg)
  have hBS : B.val ⊆ S := fun v hv =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h a ha p hp v hv⟩
  have hSconv : @IsConvex _ (T.betw k i) S := fun v₁ hv₁ v₂ hv₂ c hc =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.playerConvex_right k i p v₁ v₂ c a hc
      (Finset.mem_filter.mp hv₁).2 (Finset.mem_filter.mp hv₂).2⟩
  exact (Finset.mem_filter.mp (convClosure_sub_of_convex B S hBS hSconv hb)).2

-- ----------------------------------------------------------------
-- C.2: DevFaceLE preserved under convex closure of a single opponent
-- ----------------------------------------------------------------

/-- DevFaceLE preserved when closing a single opponent's face. -/
theorem DevFaceLE_convClosure_opp (k : ℕ) {i : I} (j : I) (hj : j ≠ i)
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).DevFaceLE i σ A B) :
    (T.game k).DevFaceLE i (Function.update σ j (T.cc k j (σ j))) A B := by
  intro a ha p hp b hb
  have hpj : p j ∈ (T.cc k j (σ j)).val := by
    have := hp j hj; rwa [Function.update_self] at this
  set S := Finset.univ.filter (fun v => ((T.game k).sign i (Function.update p j v) a b).nonneg)
  have hσS : (σ j).val ⊆ S := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h a ha (Function.update p j v)
      (fun m hm => by
        by_cases hmj : m = j
        · subst hmj; simp [Function.update_self]; exact hv
        · rw [Function.update_of_ne hmj]
          have := hp m hm; rwa [Function.update_of_ne hmj] at this)
      b hb⟩
  have hSconv : @IsConvex _ (T.betw k j) S := by
    intro v₁ hv₁ v₂ hv₂ c hc
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv₁ hv₂ ⊢
    exact T.opponentConvex k i j hj
      (Function.update p j v₁) (Function.update p j v₂) a b
      (fun m hm => by simp [Function.update_of_ne hm])
      (Function.update p j c)
      (fun m hm => by simp [Function.update_of_ne hm])
      (by simp [Function.update_self]; exact hc)
      hv₁ hv₂
  have hpS := convClosure_sub_of_convex (σ j) S hσS hSconv hpj
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hpS
  rwa [Function.update_eq_self] at hpS

-- ----------------------------------------------------------------
-- C.3: Fubini — close ALL opponent faces
-- ----------------------------------------------------------------

/-- DevFaceLE preserved under convex closure of all players' faces. -/
theorem DevFaceLE_convCloseProfile (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).DevFaceLE i σ A B) :
    (T.game k).DevFaceLE i (T.convCloseProfile k σ) A B := by
  -- Close opponents one at a time via Finset.induction (Fubini argument)
  -- Define τ_S: profile with opponents in S closed
  set τ : Finset I → Base.Profile I (T.V k) :=
    fun S j => if j ∈ S then T.cc k j (σ j) else σ j
  -- For all S ⊆ {j ≠ i}, DevFaceLE i (τ S) A B
  suffices key : ∀ S : Finset I, (∀ j ∈ S, j ≠ i) →
      (T.game k).DevFaceLE i (τ S) A B by
    -- Apply with S = univ.filter (· ≠ i), then handle player i
    have hfull := key (Finset.univ.filter (· ≠ i)) (fun j hj => by simp at hj; exact hj)
    -- convCloseProfile σ differs from τ(...) only at position i
    -- DevFaceLE only uses opponents, so the difference at i is irrelevant
    intro a ha p hp b hb
    apply hfull a ha p _ b hb
    intro m hm
    have := hp m hm
    -- τ(univ.filter(· ≠ i)) m = cc(σ m) since m ≠ i
    show p m ∈ (τ (Finset.univ.filter (· ≠ i)) m).val
    simp only [τ, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos hm]
    exact this
  intro S hS
  induction S using Finset.induction with
  | empty => convert h using 2
  | insert j S' hj ih =>
    have hjne : j ≠ i := hS j (Finset.mem_insert_self j S')
    have hS' : ∀ m ∈ S', m ≠ i := fun m hm => hS m (Finset.mem_insert_of_mem hm)
    have base := ih hS'
    have hτj : (τ S') j = σ j := by simp [τ, hj]
    -- τ (insert j S') = (τ S')[j := cc(σ j)]
    -- Apply single-opponent closure
    suffices h_eq : τ (insert j S') = Function.update (τ S') j (T.cc k j ((τ S') j)) by
      rw [h_eq]; exact T.DevFaceLE_convClosure_opp k j hjne base
    rw [hτj]; funext m
    by_cases hm : m = j
    · subst hm; simp [τ, hj, Function.update_self]
    · have := Function.update_of_ne hm (T.cc k j (σ j)) (τ S')
      rw [this]; simp [τ, Finset.mem_insert, hm]

-- ----------------------------------------------------------------
-- C.4: Nash preserved under convex closure
-- ----------------------------------------------------------------

/-- Closing all faces preserves Nash. -/
theorem IsNash_convCloseProfile (k : ℕ)
    {σ : Base.Profile I (T.V k)}
    (hN : (T.game k).IsNash σ) :
    (T.game k).IsNash (T.convCloseProfile k σ) := by
  set τ := T.convCloseProfile k σ
  intro i A hSD
  -- hSD : StrictDev i τ A, i.e., DevFaceLE i τ A (τ i) ∧ ¬DevFaceLE i τ (τ i) A
  apply hN i A
  constructor
  · -- Forward: DevFaceLE i σ A (σ i)
    -- From hSD.1: DevFaceLE i τ A (cc(σ i))
    -- right_mono with σ i ⊆ cc(σ i): DevFaceLE i τ A (σ i)
    -- antitone with σ j ⊆ τ j: DevFaceLE i σ A (σ i)
    exact DevFaceLE.antitone (T.game k) (fun j _ => face_sub_closure (σ j))
      (DevFaceLE.mono_right (T.game k) (face_sub_closure (σ i)) hSD.1)
  · -- Backward: ¬DevFaceLE i σ (σ i) A
    intro hback
    exact hSD.2 (T.DevFaceLE_convCloseProfile k (T.DevFaceLE_convClosure_left k hback))

-- ----------------------------------------------------------------
-- C.5: OD preserved under convex closure
-- ----------------------------------------------------------------

/-- Closing all faces preserves OutsideDominated for all players. -/
theorem OutsideDominated_convCloseProfile (k : ℕ)
    {σ : Base.Profile I (T.V k)}
    (h_od : ∀ j, (T.game k).OutsideDominated j σ) (i : I) :
    (T.game k).OutsideDominated i (T.convCloseProfile k σ) := by
  set τ := T.convCloseProfile k σ
  intro v' hv' w' hw'
  -- v' ∉ cc(σ i), w' ∈ cc(σ i). Need DevFaceLE i τ (vertex w') (vertex v').
  have hv'_σ : v' ∉ (σ i).val := fun hv_mem => hv' (face_sub_closure (σ i) hv_mem)
  -- For each w₀ ∈ σ i: DevFaceLE i τ (vertex w₀) (vertex v')
  have h_ext : ∀ w₀ ∈ (σ i).val,
      (T.game k).DevFaceLE i τ (Face.vertex w₀) (Face.vertex v') :=
    fun w₀ hw₀ => T.DevFaceLE_convCloseProfile k (h_od i v' hv'_σ w₀ hw₀)
  -- Unfold DevFaceLE: need sign(p, w', v') ≥ 0 for all consistent p
  intro a ha p hp b hb
  simp [Face.vertex] at ha hb
  -- ha : a = w', hb : b = v'
  rw [ha, hb]
  -- Goal: sign(p, w', v') ≥ 0
  -- Use playerConvex_left: {u : sign(p, u, v') ≥ 0} is convex, contains σ i, so contains cc(σ i)
  set S := Finset.univ.filter (fun u => ((T.game k).sign i p u v').nonneg)
  have hσS : (σ i).val ⊆ S := fun w₀ hw₀ =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      h_ext w₀ hw₀ w₀ (by simp [Face.vertex]) p hp v' (by simp [Face.vertex])⟩
  have hSconv : @IsConvex _ (T.betw k i) S := fun u₁ hu₁ u₂ hu₂ c hc =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.playerConvex_left k i p u₁ u₂ c v' hc
      (Finset.mem_filter.mp hu₁).2 (Finset.mem_filter.mp hu₂).2⟩
  exact (Finset.mem_filter.mp (convClosure_sub_of_convex (σ i) S hσS hSconv hw')).2

-- ----------------------------------------------------------------
-- C.6: DevFaceLE transfer across levels (coherence)
-- ----------------------------------------------------------------

/-- Coherence transfers DevFaceLE from coarse to fine (on embedded faces). -/
theorem DevFaceLE_embed (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).DevFaceLE i σ A B) :
    (T.game (k+1)).DevFaceLE i
      (embedProfile (T.embed k) (T.embed_inj k) σ)
      (embedFace (T.embed k i) (T.embed_inj k i) A)
      (embedFace (T.embed k i) (T.embed_inj k i) B) := by
  intro a' ha' p' hp' b' hb'
  simp only [embedFace, Finset.mem_map, Function.Embedding.coeFn_mk] at ha' hb'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨b, hb, rfl⟩ := hb'
  -- For each opponent m ≠ i, p' m ∈ (embedFace(σ m)).val = (σ m).val.map embed
  have h_opp : ∀ m, m ≠ i → ∃ u ∈ (σ m).val, T.embed k m u = p' m := by
    intro m hm
    have := hp' m hm
    simp only [embedProfile, embedFace, Finset.mem_map, Function.Embedding.coeFn_mk] at this
    exact this
  -- Build coarse profile q from preimages
  classical
  set q : Base.PureProfile I (T.V k) :=
    fun m => if hm : m = i then (T.instInhabited k m).default
             else (h_opp m hm).choose
  -- sign_irrel: replace p' by embed(q)
  have hirrel : (T.game (k+1)).sign i p' (T.embed k i a) (T.embed k i b) =
      (T.game (k+1)).sign i (embedPureProfile (T.embed k) q) (T.embed k i a) (T.embed k i b) :=
    (T.game (k+1)).sign_irrel i p' _ _ _ fun m hm => by
      simp [embedPureProfile, q, hm]; exact ((h_opp m hm).choose_spec.2).symm
  rw [hirrel, T.coherent]
  exact h a ha q (fun m hm => by simp [q, hm]; exact (h_opp m hm).choose_spec.1) b hb

-- ----------------------------------------------------------------
-- C.7: OD transfer from coarse to fine (THE MAIN TECHNICAL RESULT)
-- ----------------------------------------------------------------

/-- OD at coarse level transfers to OD at
    convCloseProfile(embedProfile(σ)) at the fine level. -/
theorem OD_embed_convClosure (k : ℕ)
    {σ : Base.Profile I (T.V k)}
    (h_od : ∀ i, (T.game k).OutsideDominated i σ) (i : I) :
    (T.game (k+1)).OutsideDominated i
      (T.convCloseProfile (k+1)
        (embedProfile (T.embed k) (T.embed_inj k) σ)) := by
  set σ' := embedProfile (T.embed k) (T.embed_inj k) σ
  set σ'' := T.convCloseProfile (k+1) σ'
  intro v' hv' w' hw'
  -- v' ∉ (σ'' i) = cc(embedFace(σ i)), w' ∈ (σ'' i)
  -- Need: DevFaceLE i σ'' (vertex w') (vertex v')
  -- i.e., ∀ p consistent with σ'', sign(p, w', v') ≥ 0
  intro a ha p hp b hb
  simp [Face.vertex] at ha hb
  -- ha : a = w', hb : b = v'
  rw [ha, hb]
  -- Goal: sign(p, w', v') ≥ 0
  -- Step 1: For w₀ ∈ (σ i), v₀ ∉ (σ i): sign(p, embed(w₀), embed(v₀)) ≥ 0
  have step1 : ∀ w₀ ∈ (σ i).val, ∀ v₀ ∉ (σ i).val,
      ((T.game (k+1)).sign i p (T.embed k i w₀) (T.embed k i v₀)).nonneg := by
    intro w₀ hw₀ v₀ hv₀
    have h_dfle := T.DevFaceLE_convCloseProfile (k+1) (T.DevFaceLE_embed k (h_od i v₀ hv₀ w₀ hw₀))
    exact h_dfle (T.embed k i w₀)
      (Finset.mem_map_of_mem _ (by simp [Face.vertex]))
      p hp (T.embed k i v₀)
      (Finset.mem_map_of_mem _ (by simp [Face.vertex]))
  -- Step 2: For w₀ ∈ (σ i): sign(p, embed(w₀), v') ≥ 0
  have step2 : ∀ w₀ ∈ (σ i).val,
      ((T.game (k+1)).sign i p (T.embed k i w₀) v').nonneg := by
    intro w₀ hw₀
    obtain ⟨b₀, hbetw⟩ := T.fine_between_embedded_at k i v' w₀
    have hb₀ : b₀ ∉ (σ i).val := T.outside_betw_witness_outside k i (σ i) w₀ hw₀ v' hv' b₀ hbetw
    have hrefl : ((T.game (k+1)).sign i p (T.embed k i w₀) (T.embed k i w₀)).nonneg := by
      rw [(T.game (k+1)).sign_refl]; exact Sign.nonneg_zero
    exact T.playerConvex_right (k+1) i p (T.embed k i w₀) (T.embed k i b₀) v'
      (T.embed k i w₀) hbetw hrefl (step1 w₀ hw₀ b₀ hb₀)
  -- Step 3: Extend w from embed(σ i) to cc(embed(σ i)) via playerConvex_left
  set S := Finset.univ.filter (fun u => ((T.game (k+1)).sign i p u v').nonneg)
  have hembS : (σ' i).val ⊆ S := by
    intro u hu
    simp only [σ', embedProfile, embedFace, Finset.mem_map, Function.Embedding.coeFn_mk] at hu
    obtain ⟨w₀, hw₀, rfl⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, step2 w₀ hw₀⟩
  have hSconv : @IsConvex _ (T.betw (k+1) i) S := fun u₁ hu₁ u₂ hu₂ c hc =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.playerConvex_left (k+1) i p u₁ u₂ c v' hc
      (Finset.mem_filter.mp hu₁).2 (Finset.mem_filter.mp hu₂).2⟩
  exact (Finset.mem_filter.mp (convClosure_sub_of_convex (σ' i) S hembS hSconv hw')).2

-- ================================================================
-- Layer D: Nash Refinement
-- ================================================================

-- ----------------------------------------------------------------
-- D.1: Refinement relation
-- ----------------------------------------------------------------

/-- A fine face F' refines a coarse face F if F' ⊆ convClosure(embed(F)). -/
def FaceRefines (k : ℕ) (i : I)
    (F' : Face (T.V (k+1) i)) (F : Face (T.V k i)) : Prop :=
  Face.IsSubface F' (T.cc (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) F))

/-- A fine profile refines a coarse profile componentwise. -/
def ProfileRefines (k : ℕ)
    (σ' : Base.Profile I (T.V (k+1)))
    (σ : Base.Profile I (T.V k)) : Prop :=
  ∀ i, T.FaceRefines k i (σ' i) (σ i)

-- ----------------------------------------------------------------
-- D.2: Convex-closed property
-- ----------------------------------------------------------------

def IsConvexClosed (k : ℕ) (σ : Base.Profile I (T.V k)) : Prop :=
  ∀ i, @IsConvex (T.V k i) (T.betw k i) (σ i).val

-- ----------------------------------------------------------------
-- D.3: Main refinement sequence
-- ----------------------------------------------------------------

/-- At every level k, there exists a Nash equilibrium that is
    OutsideDominated and convex-closed. -/
theorem nash_refining_sequence (k : ℕ) :
    ∃ σ : Base.Profile I (T.V k),
      (T.game k).IsNash σ ∧
      (∀ i, (T.game k).OutsideDominated i σ) ∧
      T.IsConvexClosed k σ := by
  induction k with
  | zero =>
    -- Start from full profile, get Nash+OD, close
    have h_od_full : ∀ i, (T.game 0).OutsideDominated i (fun _ => Face.full) :=
      fun i => OutsideDominated.maximal (T.game 0) i
    obtain ⟨τ, hτN, _, hτ_od⟩ := (T.game 0).nash_exists_sub_OD (fun _ => Face.full) h_od_full
    exact ⟨T.convCloseProfile 0 τ,
      T.IsNash_convCloseProfile 0 hτN,
      T.OutsideDominated_convCloseProfile 0 hτ_od,
      fun i => IsConvex_convClosure (τ i)⟩
  | succ n ih =>
    obtain ⟨σ_n, hN_n, hOD_n, _⟩ := ih
    -- Embed and close
    set σ_cl := T.convCloseProfile (n+1) (embedProfile (T.embed n) (T.embed_inj n) σ_n)
    -- OD at σ_cl
    have hOD_cl : ∀ i, (T.game (n+1)).OutsideDominated i σ_cl :=
      T.OD_embed_convClosure n hOD_n
    -- Get Nash ⊆ σ_cl with OD
    obtain ⟨τ, hτN, _, hτ_od⟩ := (T.game (n+1)).nash_exists_sub_OD σ_cl hOD_cl
    exact ⟨T.convCloseProfile (n+1) τ,
      T.IsNash_convCloseProfile (n+1) hτN,
      T.OutsideDominated_convCloseProfile (n+1) hτ_od,
      fun i => IsConvex_convClosure (τ i)⟩

-- ----------------------------------------------------------------
-- D.4: Refinement across adjacent levels
-- ----------------------------------------------------------------

/-- At every level k, there exists a Nash at level k+1 that refines
    a Nash at level k. -/
theorem nash_at_next_level_refines (k : ℕ) :
    ∃ σ : Base.Profile I (T.V k),
    ∃ σ' : Base.Profile I (T.V (k+1)),
      (T.game k).IsNash σ ∧
      (T.game (k+1)).IsNash σ' ∧
      T.ProfileRefines k σ' σ := by
  obtain ⟨σ_k, hN_k, hOD_k, _⟩ := T.nash_refining_sequence k
  -- Reconstruct a Nash at k+1 that refines σ_k:
  set σ_cl := T.convCloseProfile (k+1) (embedProfile (T.embed k) (T.embed_inj k) σ_k)
  have hOD_cl : ∀ i, (T.game (k+1)).OutsideDominated i σ_cl :=
    T.OD_embed_convClosure k hOD_k
  obtain ⟨τ, hτN, hτ_sub, hτ_od⟩ := (T.game (k+1)).nash_exists_sub_OD σ_cl hOD_cl
  set τ' := T.convCloseProfile (k+1) τ
  refine ⟨σ_k, τ', hN_k, T.IsNash_convCloseProfile (k+1) hτN, fun i => ?_⟩
  -- FaceRefines: τ' i = cc(τ i) ⊆ cc(σ_cl i) = cc(cc(embed(σ_k i))) = cc(embed(σ_k i))
  show Face.IsSubface (T.cc (k+1) i (τ i))
    (T.cc (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) (σ_k i)))
  have h1 : Face.IsSubface (τ i) (T.cc (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) (σ_k i))) :=
    hτ_sub i
  -- cc(τ i) ⊆ cc(cc(embed(σ_k i))) = cc(embed(σ_k i)) by mono + idempotent
  intro x hx
  have hx_cc := convClosure_mono h1 hx
  -- hx_cc : x ∈ cc(cc(embed(σ_k i))), need x ∈ cc(embed(σ_k i))
  exact convClosure_sub_of_convex _ _ (fun y hy => hy)
    (IsConvex_convClosure _) hx_cc

end GeneralSignTower

end Refinement
