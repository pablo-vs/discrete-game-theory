import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

namespace Base

/-!
# Sign games and Nash existence

This file defines **sign games** — finite games in which each player has a set of
actions and a preference ordering (not a numeric payoff) over outcomes. The ordering
is encoded as a sign function returning `pos`, `neg`, or `zero`.

The main result is `nash_exists`: every finite sign game has a Nash equilibrium
(in mixed strategies, represented as nonempty subsets of actions called *faces*).

The proof is a descent algorithm: start from the fully mixed profile (all actions
in play for every player), and iteratively remove dominated actions. The algorithm
terminates because the total number of actions across all players strictly decreases
at each step, and the key invariant `OutsideDom` is preserved.

## Main definitions and theorems
* `Sign`                    : Three-valued type: `pos | neg | zero`
* `Face V`                  : Nonempty subsets `{ S : Finset V // S.Nonempty }`
* `PureProfile I V`         : A choice of one action per player: `∀ i, V i`
* `Profile I V`             : A choice of face (mixed strategy) per player: `∀ i, Face (V i)`
* `SignGame I V`            : Cross-profile sign function with refl/antisym/trans axioms
* `Dominates i σ A B`       : Face A weakly dominates face B for player i in context σ
* `StrictDom i σ A`         : A strictly dominates σ i (dominates but is not dominated back)
* `IsNash σ`                : No player has a strict deviation: `∀ i A, ¬ StrictDom i σ A`
* `OutsideDom i σ`          : Every action outside σ i is dominated by every action inside
* `nash_exists`             : Every finite sign game has a Nash equilibrium
* `ofPayoffs`               : Construct a sign game from integer payoff functions
* `IsPureNash`              : Pure-strategy Nash: no player improves by switching action
-/

-- ================================================================
-- Section 1: Sign type
-- ================================================================

/-- A three-valued sign type representing the result of comparing two actions.
    `pos` means the first action is preferred, `neg` means the second is preferred,
    `zero` means indifference. -/
-- ANCHOR: Sign
inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign
-- ANCHOR_END: Sign
  deriving DecidableEq, Repr

namespace Sign

instance : Fintype Sign :=
  ⟨{.pos, .neg, .zero}, by intro x; cases x <;> simp⟩

/-- Negation of a sign: swaps `pos` and `neg`, fixes `zero`.
    Used to express antisymmetry: `sign(a,b) = flip(sign(b,a))`. -/
def flip : Sign → Sign
  | pos => neg
  | neg => pos
  | zero => zero

@[simp] theorem flip_pos : flip pos = neg := rfl
@[simp] theorem flip_neg : flip neg = pos := rfl
@[simp] theorem flip_zero : flip zero = zero := rfl
@[simp] theorem flip_flip (s : Sign) : s.flip.flip = s := by cases s <;> rfl

/-- `s.nonneg` holds when `s` is `pos` or `zero` (i.e., the first action is at least as good).
    This is the core predicate used in dominance comparisons. -/
def nonneg : Sign → Prop
  | pos => True
  | zero => True
  | neg => False

instance (s : Sign) : Decidable s.nonneg := by cases s <;> simp [nonneg] <;> infer_instance

@[simp] theorem nonneg_pos : pos.nonneg := trivial
@[simp] theorem nonneg_zero : zero.nonneg := trivial

lemma not_nonneg_neg : ¬neg.nonneg := id

lemma nonneg_flip_of_not_nonneg {s : Sign} (h : ¬s.nonneg) : s.flip.nonneg := by
  cases s <;> simp_all [nonneg, flip]

lemma not_nonneg_flip_of_nonneg_of_ne_zero {s : Sign} (h : s.nonneg) (hz : s ≠ zero) :
    ¬s.flip.nonneg := by
  cases s <;> simp_all [nonneg, flip]

/-- Multiplication of signs. Captures the sign of a product of reals. -/
def mul : Sign → Sign → Sign
  | zero, _ => zero
  | _, zero => zero
  | pos, s => s
  | neg, s => s.flip

@[simp] theorem mul_zero (s : Sign) : mul s zero = zero := by cases s <;> rfl
@[simp] theorem zero_mul (s : Sign) : mul zero s = zero := by rfl
@[simp] theorem mul_pos (s : Sign) : mul s pos = s := by cases s <;> rfl
@[simp] theorem pos_mul (s : Sign) : mul pos s = s := by cases s <;> rfl
@[simp] theorem neg_mul (s : Sign) : mul neg s = s.flip := by cases s <;> rfl

lemma flip_mul (s t : Sign) : (mul s t).flip = mul s.flip t := by
  cases s <;> cases t <;> rfl

lemma mul_nonneg {s t : Sign} (hs : s.nonneg) (ht : t.nonneg) : (mul s t).nonneg := by
  cases s <;> cases t <;> simp_all [mul, nonneg]

lemma nonneg_mul_flip_of_not_nonneg {s t : Sign} (hs : ¬s.nonneg) (ht : ¬t.nonneg) :
    (mul s t).nonneg := by
  cases s <;> cases t <;> simp_all [mul, nonneg, flip]

/-- Embed signs into integers: `pos ↦ 1`, `neg ↦ -1`, `zero ↦ 0`. -/
def toInt : Sign → Int
  | .pos => 1
  | .neg => -1
  | .zero => 0

@[simp] theorem toInt_pos : pos.toInt = 1 := rfl
@[simp] theorem toInt_neg : neg.toInt = -1 := rfl
@[simp] theorem toInt_zero : zero.toInt = 0 := rfl

end Sign

-- ================================================================
-- Section 1b: Comparison sign
-- ================================================================

/-- Comparison sign of two naturals: pos if a < b, neg if a > b, zero if a = b.
    Convention: cmpSign a b = pos means "b is better" (higher index preferred). -/
def cmpSign (a b : ℕ) : Sign :=
  if a < b then Sign.pos
  else if b < a then Sign.neg
  else Sign.zero

@[simp] theorem cmpSign_self (a : ℕ) : cmpSign a a = Sign.zero := by
  simp [cmpSign]

lemma cmpSign_flip (a b : ℕ) : (cmpSign a b).flip = cmpSign b a := by
  unfold cmpSign
  split <;> (split <;> simp_all [Sign.flip] <;> omega)

lemma cmpSign_nonneg_iff {a b : ℕ} : (cmpSign a b).nonneg ↔ a ≤ b := by
  unfold cmpSign
  split
  · simp [Sign.nonneg]; omega
  · split
    · simp [Sign.nonneg]; omega
    · simp [Sign.nonneg]; omega

lemma cmpSign_trans {a b c : ℕ} (h1 : (cmpSign a b).nonneg) (h2 : (cmpSign b c).nonneg) :
    (cmpSign a c).nonneg := by
  rw [cmpSign_nonneg_iff] at *; omega

-- ================================================================
-- Section 1c: Faces (nonempty finite subsets)
-- ================================================================

/--
A face is a nonempty subset of a finite set.
It represents a face of a discrete simplex, the span of the vertices it contains.
-/
@[reducible]
-- ANCHOR: Face
def Face (V : Type*) [DecidableEq V] := { S : Finset V // S.Nonempty }
-- ANCHOR_END: Face

namespace Face

variable {V : Type*} [DecidableEq V]

/-- Given an element of type V, the set {v} as a face. -/
def vertex (v : V) : Face V :=
  ⟨{v}, Finset.singleton_nonempty v⟩

@[simp] theorem vertex_val {v : V} : (vertex v : Face V).1 = {v} := rfl

/-- The full face containing all actions. Represents the maximally mixed strategy. -/
def full [Fintype V] [Nonempty V] : Face V :=
  ⟨Finset.univ, Finset.univ_nonempty⟩

@[simp] theorem full_val [Fintype V] [Nonempty V] : (full : Face V).1 = Finset.univ := rfl

/-- The mixture (union) of two faces. Represents mixing the strategies
    in A with those in B. -/
def mix (A B : Face V) : Face V :=
  ⟨A.1 ∪ B.1, A.2.mono Finset.subset_union_left⟩

@[simp] theorem mix_val {A B : Face V} : (mix A B).1 = A.1 ∪ B.1 := rfl

lemma mix_comm (A B : Face V) : mix A B = mix B A :=
  Subtype.ext (Finset.union_comm A.1 B.1)

lemma mix_idem (A : Face V) : mix A A = A :=
  Subtype.ext (Finset.union_self A.1)

lemma mix_assoc (A B C : Face V) : mix (mix A B) C = mix A (mix B C) :=
  Subtype.ext (Finset.union_assoc A.1 B.1 C.1)

/-- `IsSubface A B` means A's actions are a subset of B's actions. -/
def IsSubface (A B : Face V) : Prop := A.1 ⊆ B.1

lemma IsSubface.refl (A : Face V) : IsSubface A A := fun _ h => h

lemma IsSubface.trans {A B C : Face V} (h1 : IsSubface A B) (h2 : IsSubface B C) : IsSubface A C :=
  fun _ h => h2 (h1 h)

instance (A B : Face V) : Decidable (IsSubface A B) :=
  inferInstanceAs (Decidable (A.1 ⊆ B.1))

@[ext]
lemma ext {A B : Face V} (h : A.1 = B.1) : A = B := Subtype.ext h

instance instFintype [Fintype V] : Fintype (Face V) := by
  infer_instance

end Face

-- ================================================================
-- Section 2: Profile types
-- ================================================================

variable (I : Type*) [DecidableEq I] (V : I → Type*) [∀ i, DecidableEq (V i)]

-- ANCHOR: PureProfile
/-- A pure profile is a choice of action for each player. -/
abbrev PureProfile := ∀ i : I, V i
-- ANCHOR_END: PureProfile
-- ANCHOR: Profile
/-- A profile is a choice of face (mixed strategy) for each player. -/
abbrev Profile := ∀ i : I, Face (V i)
-- ANCHOR_END: Profile

/-- A deviation σ[i ↦ A] is a new profile in which player i selects A. -/
scoped notation σ "[" i " ↦ " A "]" => Function.update σ i A

/-- `ConsistentAt σ i p` says that pure profile `p` is consistent with mixed profile `σ`
    from player `i`'s perspective: every *opponent* `j ≠ i` plays an action within their
    face `σ j`. Player `i`'s own action in `p` is unconstrained — this reflects that
    dominance compares `i`'s alternatives while holding opponents fixed. -/
def ConsistentAt {I : Type*} {V : I → Type*} [∀ i, DecidableEq (V i)]
    (σ : Profile I V) (i : I) (p : PureProfile I V) : Prop :=
  ∀ j, j ≠ i → p j ∈ (σ j).1

/-- If `p` is consistent with `σ[i ↦ A]` at player `i`, it is also consistent with `σ`,
    since updating player `i`'s face doesn't affect opponents' faces. -/
lemma ConsistentAt.update {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]
    {σ : Profile I V} {i : I} {A : Face (V i)} {p : PureProfile I V}
    (h : ConsistentAt (σ[i ↦ A]) i p) : ConsistentAt σ i p :=
  fun j hj => by have := h j hj; rwa [Function.update_of_ne hj] at this

/-- Consistency is monotone in opponent faces: if `p` is consistent with `σ` and every
    opponent's face in `σ` is a subface of the corresponding face in `τ`, then `p` is
    consistent with `τ`. -/
lemma ConsistentAt.mono {I : Type*} {V : I → Type*} [∀ i, DecidableEq (V i)]
    {σ τ : Profile I V} {i : I} {p : PureProfile I V}
    (h : ConsistentAt σ i p) (hsub : ∀ j, j ≠ i → Face.IsSubface (σ j) (τ j)) :
    ConsistentAt τ i p :=
  fun j hj => hsub j hj (h j hj)

-- ================================================================
-- Section 3: SignGame structure
-- ================================================================

/-- An N-player sign game over player set `I` and action types `V`.

    For each player `i`, `sign i p q` returns the preference of `i` between outcome `p`
    versus outcome `q`. The result is `pos` if `p` is preferred, `neg` if `q` is preferred,
    `zero` if indifferent.

    The axioms require that preferences form a total preorder on outcomes for each player.
    The within-profile comparison `signAction` (comparing two actions holding opponents
    fixed) is derived as `sign i (p[i↦a]) (p[i↦b])`. -/
-- ANCHOR: SignGame
structure SignGame where
  sign : (i : I) → PureProfile I V → PureProfile I V → Sign
  sign_refl : ∀ i p, sign i p p = .zero
  sign_antisym : ∀ i p q, sign i p q = (sign i q p).flip
  sign_trans : ∀ i p q r, (sign i p q).nonneg → (sign i q r).nonneg →
    (sign i p r).nonneg
-- ANCHOR_END: SignGame

variable {I} {V}

namespace SignGame

variable {I : Type*} [DecidableEq I] {V : I → Type*} [∀ i, DecidableEq (V i)]
variable (G : SignGame I V)

/-- Within-profile action comparison: compares playing `a` vs `b` for player `i`,
    holding opponents fixed at `p`. Defined as `sign i (p[i↦a]) (p[i↦b])`. -/
abbrev signAction (i : I) (p : PureProfile I V) (a b : V i) : Sign :=
  G.sign i (p[i ↦ a]) (p[i ↦ b])

lemma signAction_refl (i : I) (p : PureProfile I V) (a : V i) :
    G.signAction i p a a = .zero :=
  G.sign_refl i _

lemma signAction_antisym (i : I) (p : PureProfile I V) (a b : V i) :
    G.signAction i p a b = (G.signAction i p b a).flip :=
  G.sign_antisym i _ _

lemma signAction_trans (i : I) (p : PureProfile I V) (a b c : V i)
    (hab : (G.signAction i p a b).nonneg) (hbc : (G.signAction i p b c).nonneg) :
    (G.signAction i p a c).nonneg :=
  G.sign_trans i _ _ _ hab hbc

lemma signAction_irrel (i : I) (p q : PureProfile I V) (a b : V i)
    (h : ∀ j, j ≠ i → p j = q j) :
    G.signAction i p a b = G.signAction i q a b := by
  show G.sign i (Function.update p i a) (Function.update p i b) =
       G.sign i (Function.update q i a) (Function.update q i b)
  congr 1 <;> ext j <;> by_cases hji : j = i
  · subst hji; simp [Function.update_self]
  · simp [Function.update_of_ne hji, h j hji]
  · subst hji; simp [Function.update_self]
  · simp [Function.update_of_ne hji, h j hji]

-- ================================================================
-- Section 4: Dominates
-- ================================================================

/-- Face `A` weakly dominates face `B` for player `i` in profile `σ`.

    This means: for every action `a ∈ A`, every pure profile `p` where opponents play
    within their faces in `σ`, and every action `b ∈ B`, player `i` weakly prefers `a`
    to `b`. Equivalently, every action in `A` is at least as good as every action in `B`,
    regardless of what the opponents do (within their current faces).

    This is a conservative (worst-case) notion of dominance — since we don't know the
    exact probability distribution opponents use, we require dominance against *all*
    possible opponent action combinations. -/
-- ANCHOR: Dominates
def Dominates (i : I) (σ : Profile I V) (A B : Face (V i)) : Prop :=
  ∀ a ∈ A.1, ∀ p : PureProfile I V,
    ConsistentAt σ i p → ∀ b ∈ B.1, (G.signAction i p a b).nonneg
-- ANCHOR_END: Dominates

-- ================================================================
-- Section 5: Monotonicity and transitivity
-- ================================================================

namespace Dominates

/-- Antitonicity in opponent faces: if `A` dominates `B` against the larger opponent
    profile `τ`, it also dominates against the smaller profile `σ` (where each opponent's
    face is a subface of the corresponding face in `τ`). Larger opponent faces mean more
    opponent scenarios to check, so domination against a larger profile is stronger. -/
protected lemma antitone {i : I} {σ τ : Profile I V}
    (h : ∀ j, j ≠ i → Face.IsSubface (σ j) (τ j))
    {A B : Face (V i)} (hle : G.Dominates i τ A B) :
    G.Dominates i σ A B :=
  fun a ha p hp b hb => hle a ha p (hp.mono h) b hb

/-- Left monotonicity: if `A'` dominates `B`, then any subface `A ⊆ A'` also dominates `B`,
    since fewer actions in `A` means fewer conditions to satisfy. -/
protected lemma mono_left {i : I} {σ : Profile I V} {A A' B : Face (V i)}
    (h : Face.IsSubface A A') (hle : G.Dominates i σ A' B) :
    G.Dominates i σ A B :=
  fun a ha p hp b hb => hle a (h ha) p hp b hb

/-- Right monotonicity: if `A` dominates the larger face `B'`, then `A` dominates any
    subface `B ⊆ B'`, since there are fewer actions in `B` that need to be dominated. -/
protected lemma mono_right {i : I} {σ : Profile I V} {A B B' : Face (V i)}
    (h : Face.IsSubface B B') (hle : G.Dominates i σ A B') :
    G.Dominates i σ A B :=
  fun a ha p hp b hb => hle a ha p hp b (h hb)

/-- Transitivity: if `A` dominates `B` and `B` dominates `C`, then `A` dominates `C`.
    Uses the transitivity of the underlying sign function (`sign_trans`). -/
protected lemma trans {i : I} {σ : Profile I V} {A B C : Face (V i)}
    (hAB : G.Dominates i σ A B) (hBC : G.Dominates i σ B C) :
    G.Dominates i σ A C := by
  intro a ha p hp c hc
  obtain ⟨b, hb⟩ := B.2
  exact G.signAction_trans i p a b c (hAB a ha p hp b hb) (hBC b hb p hp c hc)

end Dominates

-- ================================================================
-- Section 6: StrictDom, IsNash
-- ================================================================

/-- Player `i` has a strictly better deviation to face `A` from profile `σ`.
    This means `A` weakly dominates `σ i` (player `i`'s current face), but `σ i` does
    *not* weakly dominate `A` — so `A` is genuinely better in at least one scenario. -/
-- ANCHOR: StrictDom
def StrictDom (i : I) (σ : Profile I V) (A : Face (V i)) : Prop :=
  G.Dominates i σ A (σ i) ∧ ¬G.Dominates i σ (σ i) A

def IsNash (σ : Profile I V) : Prop :=
  ∀ (i : I) (A : Face (V i)), ¬G.StrictDom i σ A
-- ANCHOR_END: StrictDom

-- ================================================================
-- Section 7: OutsideDom
-- ================================================================

/-- The OutsideDom (outside dominated) invariant for player `i` at profile `σ`.

    `OutsideDom i σ` says that for every action `v` *outside* player `i`'s current face
    and every action `w` *inside* it, `{w}` dominates `{v}`. In other words, every excluded
    action has already been checked and found to be worse than every included action.

    This is the key invariant maintained by the Nash existence descent algorithm: it ensures
    that restricting a player's face to a dominating subface doesn't invalidate previous
    elimination steps.

    **Game-theoretic interpretation.** `OutsideDom` is the invariant of *iterated
    elimination of strictly dominated strategies* (IESDS): it is preserved under the
    descent, and a profile where it holds can be interpreted as a state of the IESDS
    algorithm in which every eliminated action is dominated by every surviving one.
    Our condition is slightly stronger than classical rationalizability, which only
    requires each eliminated action to be dominated by *some* mixed strategy. -/
-- ANCHOR: OutsideDom
def OutsideDom (i : I) (σ : Profile I V) : Prop :=
  ∀ v, v ∉ (σ i).1 → ∀ w, w ∈ (σ i).1 →
    G.Dominates i σ (Face.vertex w) (Face.vertex v)
-- ANCHOR_END: OutsideDom

-- ================================================================
-- Section 8-9: OutsideDom API
-- ================================================================

namespace OutsideDom

/-- The full profile (every player plays every action) trivially satisfies OutsideDom,
    since there are no excluded actions to check. This is the starting point of the
    Nash descent algorithm. -/
protected lemma maximal (i : I)
    [∀ j, Fintype (V j)] [∀ j, Nonempty (V j)] :
    G.OutsideDom i (fun _ => Face.full) :=
  fun v hv => absurd (Finset.mem_univ v) hv

/-- OutsideDom is preserved for the deviating player when they restrict to a subface.

    If player `i` restricts their face from `σ i` to a subface `A ⊆ σ i` that dominates
    `σ i`, then OutsideDom still holds for player `i` in the updated profile `σ[i ↦ A]`.

    The proof handles two cases for an excluded action `v`:
    - If `v` was already outside `σ i`: use the old OutsideDom hypothesis.
    - If `v` was in `σ i` but is now outside `A`: use the fact that `A` dominates `σ i`. -/
protected lemma preserved {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDom i σ)
    (h_sub : Face.IsSubface A (σ i))
    (h_dev : G.Dominates i σ A (σ i)) :
    G.OutsideDom i (σ[i ↦ A]) := by
  intro v hv w hw
  have hv' : v ∉ A.1 := by rwa [show (Function.update σ i A i).1 = A.1 from by
    simp [Function.update_self]] at hv
  have hw' : w ∈ A.1 := by rwa [show (Function.update σ i A i).1 = A.1 from by
    simp [Function.update_self]] at hw
  intro a ha_w p hp b hb_v
  have ha : a = w := Finset.mem_singleton.mp ha_w
  have hb : b = v := Finset.mem_singleton.mp hb_v
  subst ha; subst hb
  -- After subst: a replaces w, b replaces v; hw' : a ∈ A.1, hv' : b ∉ A.1
  have hp' : ConsistentAt σ i p := hp.update
  by_cases hb_in : b ∈ (σ i).1
  · exact h_dev a hw' p hp' b hb_in
  · exact h_inv b hb_in a (h_sub hw') a (Finset.mem_singleton_self _) p hp'
      b (Finset.mem_singleton_self _)

/-- OutsideDom is preserved for *other* players when player `i` restricts their face.

    If player `i` shrinks their face to `A ⊆ σ i`, then OutsideDom for any other player
    `j ≠ i` is preserved. This follows from antitonicity: shrinking an opponent's face
    makes domination *easier* (fewer opponent scenarios to check). -/
protected lemma preserved_other {i j : I} (hij : j ≠ i)
    {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDom j σ)
    (h_sub : Face.IsSubface A (σ i)) :
    G.OutsideDom j (σ[i ↦ A]) := by
  intro v hv w hw
  rw [Function.update_of_ne hij] at hv hw
  apply Dominates.antitone G (σ := σ[i ↦ A]) (τ := σ)
  · intro k hk
    by_cases hki : k = i
    · subst hki; exact fun x hx => h_sub (by rwa [Function.update_self] at hx)
    · intro x hx; rwa [Function.update_of_ne hki] at hx
  · exact h_inv v hv w hw

end OutsideDom

-- ================================================================
-- Section 10: Restricting deviations
-- ================================================================

/-- When OutsideDom holds and `σ i` does not dominate `A`, the witnessing action `b ∈ A`
    (the one that `σ i` fails to dominate) must actually lie in `σ i`.

    This is because any `b ∈ A` that is *outside* `σ i` would be dominated by every action
    in `σ i` (by OutsideDom), contradicting the fact that `b` witnesses the failure of
    domination. So the "problematic" action `b` must be inside the current face.

    This is a technical lemma used by `restrictStrictDom` to show that strict deviations
    can always be restricted to subfaces of the current face. -/
private lemma outsideDom_witness_mem {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDom i σ)
    (h_neg : ¬G.Dominates i σ (σ i) A) :
    ∃ a ∈ (σ i).1, ∃ p : PureProfile I V,
      ConsistentAt σ i p ∧
      ∃ b ∈ A.1, ¬(G.signAction i p a b).nonneg ∧ b ∈ (σ i).1 := by
  simp only [Dominates, ConsistentAt] at h_neg; push_neg at h_neg
  obtain ⟨a, ha, p, hp, b, hb, hn⟩ := h_neg
  by_cases hb_σ : b ∈ (σ i).1
  · exact ⟨a, ha, p, hp, b, hb, hn, hb_σ⟩
  · exact absurd
      (h_inv b hb_σ a ha a (Finset.mem_singleton_self _) p hp b (Finset.mem_singleton_self _))
      hn

/-- **Restriction lemma**: any strict deviation can be "restricted" to a subface of the
    current face.

    If OutsideDom holds and player `i` has a strict deviation to some face `A`, then
    `A' = A ∩ σ i` is also a strict deviation, is a proper subface of `σ i`, and
    satisfies `A' ≠ σ i`. This is crucial for the descent algorithm: it ensures each
    step strictly shrinks the deviating player's face.

    Returned as a subtype (data + proofs) rather than an existential, so it's usable
    both in proof-level arguments and in the computable `findNashOf` descent. -/
def restrictStrictDom {i : I} {σ : Profile I V} {A : Face (V i)}
    (h_inv : G.OutsideDom i σ) (h_dev : G.StrictDom i σ A) :
    { A' : Face (V i) //
      G.StrictDom i σ A' ∧ Face.IsSubface A' (σ i) ∧ A' ≠ σ i } :=
  ⟨⟨A.1 ∩ (σ i).1, by
      obtain ⟨_, h_bwd⟩ := h_dev
      obtain ⟨_, _, _, _, b, hb, _, hb_σ⟩ := outsideDom_witness_mem G h_inv h_bwd
      exact ⟨b, Finset.mem_inter.mpr ⟨hb, hb_σ⟩⟩⟩, by
    obtain ⟨h_fwd, h_bwd⟩ := h_dev
    obtain ⟨a, ha_σ, p, hp, b, hb_A, hn, hb_σ⟩ := outsideDom_witness_mem G h_inv h_bwd
    refine ⟨⟨?_, ?_⟩, Finset.inter_subset_right, ?_⟩
    · exact Dominates.mono_left G Finset.inter_subset_left h_fwd
    · intro h_contra
      exact absurd (h_contra a ha_σ p hp b (Finset.mem_inter.mpr ⟨hb_A, hb_σ⟩)) hn
    · intro heq
      have h_σ_sub_A : Face.IsSubface (σ i) A := by
        intro x hx; exact (Finset.mem_inter.mp (heq ▸ hx)).1
      apply h_bwd
      intro x hx p' hp' y hy
      by_cases hy_σ : y ∈ (σ i).1
      · exact (Dominates.mono_left G h_σ_sub_A h_fwd) x hx p' hp' y hy_σ
      · exact h_inv y hy_σ x hx x (Finset.mem_singleton_self _) p' hp'
          y (Finset.mem_singleton_self _)⟩

-- ================================================================
-- Section 11: Profile size and descent
-- ================================================================

omit G in
/-- The total number of actions across all players' faces. Used as the termination
    measure for the Nash descent algorithm — each step strictly decreases this value. -/
def profileSize [Fintype I] (σ : Profile I V) : ℕ :=
  Finset.univ.sum (fun i => (σ i).1.card)

omit G in
/-- Replacing one player's face with a proper subface strictly decreases the profile size. -/
lemma profileSize_decreases [Fintype I] {i : I} {σ : Profile I V} {A : Face (V i)}
    (hsub : Face.IsSubface A (σ i)) (hne : A ≠ σ i) :
    profileSize (σ[i ↦ A]) < profileSize σ := by
  unfold profileSize
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hji : j = i
    · subst hji; simp only [Function.update_self]; exact Finset.card_le_card hsub
    · rw [Function.update_of_ne hji]
  · exact ⟨i, Finset.mem_univ i, by
      simp only [Function.update_self]
      exact Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (Face.ext h)⟩)⟩

-- ================================================================
-- Section 12: Nash existence
-- ================================================================

/-- **Nash existence from OutsideDom**: given any profile satisfying the OutsideDom
    invariant, there exists a Nash equilibrium. Additionally tracks that the resulting
    Nash profile `τ` is a subprofile of the starting profile `σ` and still satisfies
    `OutsideDom`.

    This is the core of the Nash existence proof. The algorithm:
    1. If `σ` is already Nash, return it.
    2. Otherwise, some player `i` has a strict deviation to `A`.
    3. By `restrictStrictDom`, get `A' ⊆ σ i` with `A' ≠ σ i` that is still a strict
       deviation.
    4. Update `σ[i ↦ A']`. OutsideDom is preserved (by `preserved` and `preserved_other`).
    5. Profile size strictly decreases, so recurse.

    Termination is guaranteed because `profileSize` is a natural number that decreases
    at each step. For a directly executable version, see `findNashOf` below. -/
theorem nash_exists_sub_of_outsideDom [Fintype I]
    (σ : Profile I V)
    (h_od : ∀ i, G.OutsideDom i σ) :
    ∃ τ, G.IsNash τ ∧ (∀ i, Face.IsSubface (τ i) (σ i)) ∧
      (∀ i, G.OutsideDom i τ) := by
  by_cases h : G.IsNash σ
  · exact ⟨σ, h, fun _ x hx => hx, h_od⟩
  · simp only [IsNash, not_forall, not_not] at h
    obtain ⟨i₀, A, hA⟩ := h
    obtain ⟨A', hdev, hsub, hne⟩ := G.restrictStrictDom (h_od i₀) hA
    have hdec := profileSize_decreases hsub hne
    have h_od' : ∀ j, G.OutsideDom j (σ[i₀ ↦ A']) := fun j => by
      by_cases hij : j = i₀
      · subst hij; exact OutsideDom.preserved G (h_od j) hsub hdev.1
      · exact OutsideDom.preserved_other G hij (h_od j) hsub
    obtain ⟨τ, hτN, hτ_sub, hτ_od⟩ := nash_exists_sub_of_outsideDom (σ[i₀ ↦ A']) h_od'
    refine ⟨τ, hτN, fun j => ?_, hτ_od⟩
    by_cases hji : j = i₀
    · subst hji
      intro x hx
      have hx' := hτ_sub j hx
      rw [Function.update_self] at hx'
      exact hsub hx'
    · intro x hx
      have := hτ_sub j hx
      rwa [Function.update_of_ne hji] at this
  termination_by profileSize σ

/-- **Main theorem**: every finite sign game has a Nash equilibrium.
    Proved by starting from the fully mixed profile and applying the descent algorithm.

    This is the *existence* statement — it uses `Classical.em` internally (via `by_cases`
    on `IsNash`) and so is not directly executable. For an actual `#eval`-able function
    returning a Nash profile, see `findNash` below, which requires `LinearOrder` on the
    player and action types to make the deviation search computable. -/
-- ANCHOR: nash_exists
theorem nash_exists [Fintype I] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] :
    ∃ σ, G.IsNash σ :=
-- ANCHOR_END: nash_exists
  (G.nash_exists_sub_of_outsideDom (fun _ => Face.full)
    (fun i => OutsideDom.maximal G i)).imp (fun _ h => h.1)

-- ================================================================
-- Section 13b: Computable Nash descent
-- ================================================================

/-!
The existential theorems above (`nash_exists`, `nash_exists_sub_of_outsideDom`) are not
directly executable: they're `theorem`s, and the descent uses `by_cases` on `IsNash` which
falls back to `Classical.em`. This section provides their computable counterparts — `def`s
`findNash` and `findNashOf` returning an actual Nash profile, ready for `#eval`.

The algorithm is literally the same descent. The only differences are:
* `Decidable` instances for `Dominates`, `StrictDom`, `IsNash` (so we can branch on
  `IsNash` without invoking classical logic);
* a computable search `findDev` that finds a strict deviation via `Finset.sort` +
  `List.sublists` — this is why the computable versions require `LinearOrder` on `I` and
  on each `V i`, while the existence theorems need only `Fintype`.

The underlying `restrictStrictDom` is shared between both paths: it was already written as
a computable `def` returning a subtype, so the existence theorems destructure it the same
way they would destructure an existential.
-/

section Computable

variable [Fintype I] [∀ i, Fintype (V i)]
variable [LinearOrder I] [∀ i, LinearOrder (V i)]

/-- `Dominates` is decidable given finiteness of players and actions. -/
instance Dominates.instDecidable (i : I) (σ : Profile I V) (A B : Face (V i)) :
    Decidable (G.Dominates i σ A B) := by
  unfold Dominates ConsistentAt
  infer_instance

/-- `StrictDom` is decidable. -/
instance StrictDom.instDecidable (i : I) (σ : Profile I V) (A : Face (V i)) :
    Decidable (G.StrictDom i σ A) := by
  unfold StrictDom
  infer_instance

/-- `IsNash` is decidable. -/
instance IsNash.instDecidable (σ : Profile I V) : Decidable (G.IsNash σ) := by
  unfold IsNash
  infer_instance

/-- Convert a list of vertices into a face, given a proof that it's nonempty. -/
private def listToFace {V : Type*} [DecidableEq V] (l : List V) (h : l ≠ []) : Face V :=
  ⟨l.toFinset, by
    cases l with
    | nil => exact absurd rfl h
    | cons v _ => exact ⟨v, List.mem_toFinset.mpr List.mem_cons_self⟩⟩

/-- Computable search for a strict deviation at a single player. Iterates over all nonempty
    subfaces of `σ i` via `List.sublists` of the sorted vertex list. -/
def findDevAt (σ : Profile I V) (i : I) : Option (Face (V i)) :=
  ((σ i).1.sort (· ≤ ·)).sublists.findSome? fun sub =>
    if hne : sub ≠ [] then
      let A : Face (V i) := listToFace sub hne
      if G.StrictDom i σ A then some A else none
    else none

/-- Computable search for a strict deviation in `σ`. Iterates players in sorted order;
    for each player, iterates subfaces of `σ i` via `List.sublists`. -/
def findDev (σ : Profile I V) : Option ((i : I) × Face (V i)) :=
  ((Finset.univ : Finset I).sort (· ≤ ·)).findSome? fun i =>
    (G.findDevAt σ i).map fun A => ⟨i, A⟩

lemma findDevAt_eq_some_strictDom {σ : Profile I V} {i : I} {A : Face (V i)}
    (h : G.findDevAt σ i = some A) : G.StrictDom i σ A := by
  unfold findDevAt at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, sub, _, _, hfa, _⟩ := h
  by_cases hne : sub ≠ []
  · rw [dif_pos hne] at hfa
    by_cases hsd : G.StrictDom i σ (listToFace sub hne)
    · rw [if_pos hsd] at hfa
      have heq : listToFace sub hne = A := Option.some.inj hfa
      exact heq ▸ hsd
    · rw [if_neg hsd] at hfa; cases hfa
  · rw [dif_neg hne] at hfa; cases hfa

lemma findDev_eq_some_strictDom {σ : Profile I V} {x : (i : I) × Face (V i)}
    (h : G.findDev σ = some x) : G.StrictDom x.1 σ x.2 := by
  unfold findDev at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, i, _, _, hi, _⟩ := h
  match hfd : G.findDevAt σ i, hi with
  | none, hi => rw [Option.map_none] at hi; cases hi
  | some A, hi =>
      rw [Option.map_some] at hi
      obtain rfl : x = ⟨i, A⟩ := (Option.some.inj hi).symm
      exact G.findDevAt_eq_some_strictDom hfd

/-- If no proper subface of `σ i` is found by `findDevAt`, and `OutsideDom` holds at `i`,
    then no face is a strict deviation for player `i`. -/
lemma findDevAt_eq_none_no_strictDom {σ : Profile I V} {i : I}
    (h_od : G.OutsideDom i σ) (h : G.findDevAt σ i = none)
    {A : Face (V i)} (hStrict : G.StrictDom i σ A) : False := by
  -- By restrictStrictDom, there is a subface A' ⊆ σ i, A' ≠ σ i, which is a strict dev.
  obtain ⟨A', hA'dev, hA'sub, _⟩ := G.restrictStrictDom h_od hStrict
  -- A'.1 is a nonempty subset of (σ i).1. Let sub = (σ i).1.sort.filter (· ∈ A'.1).
  -- sub is a sublist of (σ i).1.sort, and sub.toFinset = A'.1.
  let l := (σ i).1.sort (· ≤ ·)
  let sub := l.filter (· ∈ A'.1)
  have hsub_sub : sub ∈ l.sublists := by
    rw [List.mem_sublists]
    exact List.filter_sublist
  have hsub_ne : sub ≠ [] := by
    obtain ⟨v, hv⟩ := A'.2
    intro hcontra
    have : v ∈ sub := by
      simp only [sub, List.mem_filter, decide_eq_true_eq]
      refine ⟨?_, hv⟩
      simp only [l, Finset.mem_sort]
      exact hA'sub hv
    rw [hcontra] at this
    exact List.not_mem_nil this
  have hsub_toFinset : sub.toFinset = A'.1 := by
    ext x
    simp only [sub, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, l, Finset.mem_sort]
    constructor
    · rintro ⟨_, hx⟩; exact hx
    · intro hx; exact ⟨hA'sub hx, hx⟩
  -- Now show findDevAt would have returned some at this sublist
  unfold findDevAt at h
  rw [List.findSome?_eq_none_iff] at h
  specialize h sub hsub_sub
  simp only [hsub_ne, ne_eq, not_false_eq_true, ↓reduceDIte] at h
  -- h says the if branch returned none, so strict dom fails
  have hface_eq : listToFace sub hsub_ne = A' := by
    apply Subtype.ext
    show sub.toFinset = A'.1
    exact hsub_toFinset
  rw [hface_eq, if_pos hA'dev] at h
  exact Option.some_ne_none _ h

lemma findDev_eq_none_isNash {σ : Profile I V} (h_od : ∀ i, G.OutsideDom i σ)
    (h : G.findDev σ = none) : G.IsNash σ := by
  intro i A hStrict
  unfold findDev at h
  rw [List.findSome?_eq_none_iff] at h
  have hmem : i ∈ (Finset.univ : Finset I).sort (· ≤ ·) := by
    rw [Finset.mem_sort]; exact Finset.mem_univ _
  specialize h i hmem
  match hfd : G.findDevAt σ i with
  | none => exact G.findDevAt_eq_none_no_strictDom (h_od i) hfd hStrict
  | some A' =>
      rw [hfd] at h
      simp at h

/-- **Computable Nash descent**: given a profile satisfying `OutsideDom`, returns an actual
    Nash equilibrium as data (subtype). This is the executable counterpart of
    `nash_exists_sub_of_outsideDom` — same algorithm, but with decidable branching and a
    sorted search instead of `by_cases` + `Classical.em`, at the cost of requiring
    `LinearOrder I` and `LinearOrder (V i)`. -/
def findNashOf (σ : Profile I V) (h_od : ∀ i, G.OutsideDom i σ) :
    { τ : Profile I V // G.IsNash τ } :=
  match hfd : G.findDev σ with
  | none => ⟨σ, G.findDev_eq_none_isNash h_od hfd⟩
  | some ⟨i₀, A⟩ =>
      have hdev : G.StrictDom i₀ σ A := G.findDev_eq_some_strictDom hfd
      let r := G.restrictStrictDom (h_od i₀) hdev
      have hsub : Face.IsSubface r.1 (σ i₀) := r.2.2.1
      have hne : r.1 ≠ σ i₀ := r.2.2.2
      have hdec : profileSize (σ[i₀ ↦ r.1]) < profileSize σ :=
        profileSize_decreases hsub hne
      findNashOf (σ[i₀ ↦ r.1]) (fun j => by
        by_cases hij : j = i₀
        · subst hij; exact OutsideDom.preserved G (h_od j) hsub r.2.1.1
        · exact OutsideDom.preserved_other G hij (h_od j) hsub)
  termination_by profileSize σ

/-- **Computable Nash existence**: starting from the fully mixed profile, returns a Nash
    equilibrium as data. Executable counterpart of `nash_exists`; can be `#eval`-ed directly
    on a concrete `SignGame`. See `findNashOf` for the version with an arbitrary starting
    profile. -/
-- ANCHOR: findNash
def findNash [Nonempty I] [∀ i, Nonempty (V i)] :
    { σ : Profile I V // G.IsNash σ } :=
-- ANCHOR_END: findNash
  G.findNashOf (fun _ => Face.full) (fun i => OutsideDom.maximal G i)

end Computable

-- ================================================================
-- Section 14: Building SignGame from payoffs
-- ================================================================

/-- Construct a `SignGame` from integer-valued payoff functions.

    Given payoff functions `u i : (∀ j, V j) → Int` for each player `i`, the sign between
    actions `a` and `b` for player `i` at profile `p` is determined by comparing `u i (p[i ↦ a])`
    with `u i (p[i ↦ b])`: positive if `a` gives higher payoff, negative if `b` does, zero
    if equal. The resulting sign game depends only on the *ordinal ranking* of payoffs — any
    strictly monotone transformation of each player's payoffs produces the same game
    (see `ofPayoffs_strictMono_invariant` in `Invariance.lean`). -/
def ofPayoffs [Fintype I]
    (u : (i : I) → PureProfile I V → Int) : SignGame I V where
  sign i p q :=
    if u i p > u i q then .pos
    else if u i p = u i q then .zero
    else .neg
  sign_refl i p := by simp
  sign_antisym i p q := by
    simp only [Sign.flip]
    split_ifs <;> first | rfl | omega
  sign_trans i p q r := by
    simp only [Sign.nonneg]
    split_ifs <;> simp_all; omega

-- ================================================================
-- Section 15: Pure Nash and examples
-- ================================================================

/-- A pure profile `p` is a pure Nash equilibrium if no player can improve by switching
    to any other action, holding all opponents fixed. Equivalently, `sign i p (p i) v ≥ 0`
    for all players `i` and alternative actions `v`. -/
def IsPureNash (p : PureProfile I V) : Prop :=
  ∀ (i : I) (v : V i), (G.signAction i p (p i) v).nonneg

end SignGame

end Base
