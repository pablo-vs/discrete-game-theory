import VersoManual
import DiscreteGameTheory.Refinement
import DiscreteGameTheory.Invariance

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "."
set_option verso.exampleModule "DiscreteGameTheory.Refinement"

open Base Refinement

#doc (Manual) "Refinement Towers" =>
%%%
tag := "refinement-towers"
%%%

The theory so far keeps only ordinal information — which action
is better, not by how much.
We add back cardinal information in a controlled way, by refining
the action space into finer levels where different mixtures can
be distinguished.

At level 0, each player's strategy space is just their action set.
At each subsequent level, new actions appear between existing ones.
A betweenness relation tracks which actions lie between which
others, and convexity axioms ensure that domination extends
smoothly from embedded points to interpolated ones.

# Betweenness and Convexity

An abstract betweenness relation says when a point lies on the
segment between two others:

```anchor Betweenness
class Betweenness (V : Type*) where
  between : V → V → V → Prop
  between_refl_left : ∀ a b, between a a b
  between_refl_right : ∀ a b, between b a b
  between_symm : ∀ a b c, between c a b → between c b a
  between_self : ∀ a c, between c a a → c = a
  between_dec : ∀ c a b, Decidable (between c a b)
```

Endpoints are always between themselves, the relation is symmetric
in the endpoints, and between `a` and `a` only lies `a` itself.

A set is _convex_ when it contains every point between any two
of its members:

```anchor IsConvex
def IsConvex (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c, Betweenness.between c a b → c ∈ S
```

The _convex closure_ of a face is the smallest convex superset —
computable, using `Finset.filter` over all convex supersets:

```anchor convClosure
def convClosure (F : Face V) : Face V :=
  ⟨Finset.univ.filter (fun v =>
      ∀ S : Finset V, F.val ⊆ S → IsConvex S → v ∈ S),
   let ⟨x, hx⟩ := F.property
   ⟨x, Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, fun _S hFS _ => hFS hx⟩⟩⟩
```

A key proof pattern: if a predicate holds on a face and is
preserved by betweenness, it holds on the convex closure. The
lemma `convClosure_pred` encapsulates the common technique of
filtering by a predicate, showing the result is convex, and
applying `convClosure_sub_of_convex`.

# The Sign Tower

A *sign tower* is a sequence of sign games at increasing precision
levels, connected by embeddings and convexity axioms. The full
`SignTower` structure has many fields; the key ones are:

```lean -show
namespace Docs
variable (I : Type*) [DecidableEq I] [Fintype I]
```

```lean
structure SignTowerKey where
  V : ℕ → I → Type*
  game : (k : ℕ) → SignGame I (V k)
  embed : ∀ k i, V k i → V (k+1) i
  coherent :
    ∀ k i p a b,
      (game (k+1)).sign i
        (embedPureProfile (embed k) p)
        (embed k i a) (embed k i b) =
      (game k).sign i p a b
  /- ... playerConvex, opponentConvex,
     fine_between_embedded_at ... -/
```

```lean -show
end Docs
```

Each level k has action types, a sign game, and an injection
into level k+1. The axioms ensure the tower is well-behaved:

- `coherent` — signs at embedded points match the coarse level:
  evaluating the fine sign function on embedded arguments gives
  the same result as the coarse sign function.
- `playerConvex_left` (and `playerConvex_right`) — the sets of
  actions that are nonneg-signed against a fixed action are
  convex, allowing domination to extend from embedded points to
  convex closures.
- `opponentConvex` — sign is convex in each opponent's action,
  the "Fubini" direction for closing all opponents' faces one
  at a time.
- `fine_between_embedded_at` — every fine action lies between
  two embedded coarse actions, the spanning condition that
  ensures no fine point escapes the reach of OD transfer.

# OD Transfer Across Levels

The main technical result: if every player satisfies {ref "outside-dom"}[OutsideDom]. at
level k, they still satisfy OD at level k+1 after embedding
and convex closure.

```anchor outsideDom_embed_convClosure
theorem outsideDom_embed_convClosure (k : ℕ)
    {σ : Base.Profile I (T.V k)}
    (h_od : ∀ i, (T.game k).OutsideDom i σ)
    (i : I) :
    (T.game (k+1)).OutsideDom i
      (T.convexClosureProfile (k+1)
        (embedProfile
          (T.embed k) (T.embed_inj k) σ)) := by
```

The proof handles three cases for showing that sign is nonneg
where w' is inside and v' is outside the closed embedded face:

1. _Embedded inside vs embedded outside_: use coherence to
   reduce to the coarse level, apply OD.
2. _Embedded inside vs arbitrary outside_: the spanning axiom
   places v' between two embedded points, then player convexity
   interpolates the sign.
3. _Arbitrary inside vs outside_: extend from step 2 via
   `convClosure_pred` on the player's convex closure.

This is where all three convexity axioms and the spanning axiom
earn their keep.

# Nash Refinement

At every level k, there exists a Nash equilibrium that is OD
and has convex faces:

```anchor nash_refining_sequence
theorem nash_refining_sequence (k : ℕ) :
    ∃ σ : Base.Profile I (T.V k),
      (T.game k).IsNash σ ∧
      (∀ i, (T.game k).OutsideDom i σ) ∧
      T.HasConvexFaces k σ := by
```

The proof is by induction. At level 0, start from the full
profile (vacuously OD), run the descent algorithm, and
convex-close the result. At level k+1, embed the level-k Nash
equilibrium, take its convex closure, transfer OD via
`outsideDom_embed_convClosure`, run descent again, and
convex-close.

Moreover, Nash equilibria at adjacent levels are compatible —
the fine-level equilibrium refines the coarse-level one:

```anchor nash_at_next_level_refines
theorem nash_at_next_level_refines (k : ℕ) :
    ∃ σ : Base.Profile I (T.V k),
    ∃ σ' : Base.Profile I (T.V (k+1)),
      (T.game k).IsNash σ ∧
      (T.game (k+1)).IsNash σ' ∧
      T.ProfileRefines k σ' σ := by
```

A profile _refines_ another when each player's fine face is
contained in the convex closure of the embedded coarse face:

```anchor ProfileRefines
def ProfileRefines (k : ℕ)
    (σ' : Base.Profile I (T.V (k+1)))
    (σ : Base.Profile I (T.V k)) : Prop :=
  ∀ i, T.FaceRefines k i (σ' i) (σ i)
```

The equilibrium "zooms in" — it narrows down which region of
each player's action space is in play.

# Invariance

Sign games are determined by their sign functions — two games
with the same signs on all inputs are equal:

```anchor SignGame.ext' (module := DiscreteGameTheory.Invariance)
@[ext]
lemma SignGame.ext' {G H : SignGame I V}
    (h : ∀ i p a b,
      G.sign i p a b = H.sign i p a b) :
    G = H := by
```

At level 0, any per-player strictly monotone transformation
of payoffs preserves the sign game. Nash equilibria depend only
on the ordinal ranking of payoffs, not their cardinal values:

```anchor ofPayoffs_strictMono_invariant (module := DiscreteGameTheory.Invariance)
theorem ofPayoffs_strictMono_invariant [Fintype I]
    (u : (i : I) → (∀ j, V j) → Int)
    (f : (i : I) → Int → Int)
    (hf : ∀ i, StrictMono (f i)) :
    SignGame.ofPayoffs (fun i q => f i (u i q)) =
    SignGame.ofPayoffs u := by
```

At higher refinement levels, the convexity structure introduces
cardinal content. The invariance group shrinks: only
transformations that preserve betweenness (such as positive
affine maps) leave the tower unchanged. In the limit, this
recovers the von Neumann–Morgenstern uniqueness class — exactly
the positive affine transformations.
