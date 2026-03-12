import DiscreteGameTheory.Base

/-!
# Refinement Tower for N-Player Sign Games

A tower of sign games at increasing precision levels, connected by embeddings and
convexity axioms. In the base theory, the only mixture of actions `a` and `b` is `{a,b}`.
Increasing precision means that different mixtures can be distinguished, for example
"a mixture of `a` and `b`, where `a` has greater weight".

The key idea: the discrete simplex at each level is an abstract
convex space (via a betweenness relation), and domination/OD transfer across levels
because the convexity axioms ensure that closing faces preserves these properties.

## Main definitions

* `Betweenness`: abstract betweenness relation on a type
* `IsConvex`, `convClosure`: convex sets and smallest convex superset
* `SignTower`: tower of sign games with embedding, coherence, and convexity axioms
* `FaceRefines`, `ProfileRefines`: refinement relations across adjacent levels
* `HasConvexFaces`: all players' faces are convex in the grid's betweenness

## Main results

* `outsideDom_embed_convClosure`: OD transfers from coarse to fine level —
  the main technical result that makes the tower work.
* `nash_refining_sequence`: Nash + OD + convex-closed at every level k.
* `nash_at_next_level_refines`: fine Nash refines coarse Nash.

## Proof architecture

The transfer chain for the inductive step of `nash_refining_sequence`:

    OD at level k
    → OD on embedded faces at level k+1           (Dominates_embed)
    → OD on convex closures at level k+1           (outsideDom_embed_convClosure)
    → Nash via descent at level k+1                (nash_exists_sub_of_outsideDom)
    → convex-close the result                      (IsNash_convexClosureProfile)

The hardest step is `outsideDom_embed_convClosure`, which needs all three
convexity axioms (playerConvex_left/right, opponentConvex) plus the spanning
axiom (fine_between_embedded_at).
-/

namespace Refinement

open Base (Sign Face cmpSign)
open Base.SignGame (Dominates OutsideDom)

/-- A betweenness relation on a type. `between c a b` means c lies
    on the segment from a to b. -/
-- ANCHOR: Betweenness
class Betweenness (V : Type*) where
  between : V → V → V → Prop
  between_refl_left : ∀ a b, between a a b
  between_refl_right : ∀ a b, between b a b
  between_symm : ∀ a b c, between c a b → between c b a
  between_self : ∀ a c, between c a a → c = a
  between_dec : ∀ c a b, Decidable (between c a b)
-- ANCHOR_END: Betweenness

attribute [instance] Betweenness.between_dec

section ConvexClosure

variable {V : Type*} [DecidableEq V] [Fintype V] [Betweenness V]

-- ANCHOR: IsConvex
def IsConvex (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c, Betweenness.between c a b → c ∈ S
-- ANCHOR_END: IsConvex

instance IsConvex.decidable (S : Finset V) : Decidable (IsConvex S) :=
  inferInstanceAs (Decidable (∀ a ∈ S, ∀ b ∈ S, ∀ c, Betweenness.between c a b → c ∈ S))

/-- Smallest convex superset, defined as the intersection of all convex supersets. -/
-- ANCHOR: convClosure
def convClosure (F : Face V) : Face V :=
  ⟨Finset.univ.filter (fun v =>
      ∀ S : Finset V, F.val ⊆ S → IsConvex S → v ∈ S),
   let ⟨x, hx⟩ := F.property
   ⟨x, Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, fun _S hFS _ => hFS hx⟩⟩⟩
-- ANCHOR_END: convClosure

lemma mem_convClosure (F : Face V) (v : V) :
    v ∈ (convClosure F).val ↔ ∀ S : Finset V, F.val ⊆ S → IsConvex S → v ∈ S := by
  simp [convClosure, Finset.mem_filter]

lemma face_sub_closure (F : Face V) :
    Face.IsSubface F (convClosure F) :=
  fun _ hv => (mem_convClosure F _).mpr (fun _ hFS _ => hFS hv)

lemma convClosure_sub_of_convex (F : Face V) (S : Finset V)
    (hFS : F.val ⊆ S) (hS : IsConvex S) :
    (convClosure F).val ⊆ S :=
  fun _ hv => (mem_convClosure F _).mp hv S hFS hS

lemma IsConvex_convClosure (F : Face V) :
    IsConvex (convClosure F).val := by
  intro a ha b hb c hc
  rw [mem_convClosure] at ha hb ⊢
  intro S hFS hS
  exact hS a (ha S hFS hS) b (hb S hFS hS) c hc

lemma convClosure_idempotent (F : Face V) :
    convClosure (convClosure F) = convClosure F := by
  apply Face.ext; ext v
  constructor
  · intro hv
    exact convClosure_sub_of_convex (convClosure F) (convClosure F).val
      (fun x hx => hx) (IsConvex_convClosure F) hv
  · intro hv
    exact face_sub_closure (convClosure F) hv

lemma convClosure_mono {F G : Face V}
    (h : Face.IsSubface F G) :
    Face.IsSubface (convClosure F) (convClosure G) := by
  intro v hv
  rw [mem_convClosure] at hv ⊢
  intro S hGS hS
  exact hv S (fun x hx => hGS (h hx)) hS

lemma convClosure_of_convex {F : Face V}
    (h : IsConvex F.val) :
    convClosure F = F := by
  apply Face.ext; ext v
  constructor
  · intro hv; exact convClosure_sub_of_convex F F.val (fun x hx => hx) h hv
  · intro hv; exact face_sub_closure F hv

/-- If a predicate holds on a face and is preserved by betweenness,
    it holds on the convex closure. Encapsulates the common "filter by predicate,
    show convex, apply `convClosure_sub_of_convex`" pattern. -/
lemma convClosure_pred (F : Face V) (pred : V → Prop) [DecidablePred pred]
    (hF : ∀ v ∈ F.val, pred v)
    (hconv : ∀ v₁ v₂ c, pred v₁ → pred v₂ → Betweenness.between c v₁ v₂ → pred c)
    {v : V} (hv : v ∈ (convClosure F).val) : pred v := by
  set S := Finset.univ.filter (fun v => pred v)
  have hFS : F.val ⊆ S := fun v hv =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF v hv⟩
  have hSconv : IsConvex S := fun v₁ hv₁ v₂ hv₂ c hc =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconv v₁ v₂ c
      (Finset.mem_filter.mp hv₁).2 (Finset.mem_filter.mp hv₂).2 hc⟩
  exact (Finset.mem_filter.mp (convClosure_sub_of_convex F S hFS hSconv hv)).2

end ConvexClosure

-- ================================================================
-- Embedding infrastructure
-- ================================================================

variable {I : Type*} [DecidableEq I] [Fintype I]

def embedPureProfile {V₀ V₁ : I → Type*}
    (emb : ∀ i, V₀ i → V₁ i) (p : Base.PureProfile I V₀) :
    Base.PureProfile I V₁ :=
  fun i => emb i (p i)

def embedFace {W₀ W₁ : Type*} [DecidableEq W₀] [DecidableEq W₁]
    (emb_i : W₀ → W₁) (emb_inj : Function.Injective emb_i)
    (F : Face W₀) : Face W₁ :=
  ⟨F.val.map ⟨emb_i, emb_inj⟩,
   let ⟨x, hx⟩ := F.property; ⟨emb_i x, Finset.mem_map_of_mem _ hx⟩⟩

def embedProfile {V₀ V₁ : I → Type*}
    [∀ i, DecidableEq (V₀ i)] [∀ i, DecidableEq (V₁ i)]
    (emb : ∀ i, V₀ i → V₁ i)
    (emb_inj : ∀ i, Function.Injective (emb i))
    (σ : Base.Profile I V₀) : Base.Profile I V₁ :=
  fun i => embedFace (emb i) (emb_inj i) (σ i)

-- ================================================================
-- Sign Tower
-- ================================================================

/-- A tower of sign games at increasing precision levels, connected by embeddings.

    Each level k has action types `V k i`, a sign game `game k`, and an embedding
    `embed k` into level k+1. The axioms ensure the tower is well-behaved:

    - **coherent**: signs at embedded points match coarse signs
    - **playerConvex_left/right**: `{v : sign(p, v, x) ≥ 0}` and `{v : sign(p, x, v) ≥ 0}`
      are convex — needed to extend domination from embedded points to convex closures
    - **opponentConvex**: sign is convex in each opponent's action — the "Fubini" direction
      for closing all opponents' faces one at a time
    - **fine_between_embedded_at**: every fine point lies between two embedded coarse points —
      the spanning condition that lets OD transfer handle non-embedded outside points -/
structure SignTower (I : Type*) [DecidableEq I] [Fintype I] where
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
  /-- Every fine action lies between two embedded coarse actions (spanning). -/
  fine_between_embedded_at : ∀ k i (v : V (k+1) i) (a : V k i),
    ∃ b : V k i, (betw (k+1) i).between v (embed k i a) (embed k i b)

namespace SignTower

variable {I : Type*} [DecidableEq I] [Fintype I]
variable (T : SignTower I)

instance instDE (k : ℕ) (i : I) : DecidableEq (T.V k i) := T.instDecEq k i
instance instFT (k : ℕ) (i : I) : Fintype (T.V k i) := T.instFintype k i
instance instInh (k : ℕ) (i : I) : Inhabited (T.V k i) := T.instInhabited k i
instance instNE (k : ℕ) (i : I) : Nonempty (T.V k i) := ⟨default⟩
instance instBW (k : ℕ) (i : I) : Betweenness (T.V k i) := T.betw k i

def convexClosureProfile (k : ℕ)
    (σ : Base.Profile I (T.V k)) :
    Base.Profile I (T.V k) :=
  fun i => @convClosure (T.V k i) (T.instDecEq k i) (T.instFintype k i)
    (T.betw k i) (σ i)

def faceClosure (k : ℕ) (i : I) (F : Face (T.V k i)) : Face (T.V k i) :=
  @convClosure (T.V k i) (T.instDecEq k i) (T.instFintype k i) (T.betw k i) F

-- ================================================================
-- Transfer theorems: Dominates and OD under closure and embedding
-- ================================================================

/-- Dominates is insensitive to player i's own face in the profile,
    since `ConsistentAt` only checks opponents j ≠ i. -/
lemma Dominates_update_self (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {F : Face (T.V k i)}
    {A B : Face (T.V k i)} :
    (T.game k).Dominates i (Function.update σ i F) A B ↔
    (T.game k).Dominates i σ A B := by
  constructor
  · intro h a ha p hp b hb
    exact h a ha p (fun m hm => by
      rw [Function.update_of_ne hm]; exact hp m hm) b hb
  · intro h a ha p hp b hb
    exact h a ha p (fun m hm => by
      have := hp m hm; rw [Function.update_of_ne hm] at this; exact this) b hb

/-- If v is between embed(w₀) and embed(b), w₀ ∈ F, and v ∉ faceClosure(embed(F)),
    then b ∉ F. (If b ∈ F, both endpoints are inside faceClosure, so v ∈ faceClosure by
    convexity, contradicting the hypothesis.) -/
lemma outside_betw_witness_outside (k : ℕ) (i : I)
    (F : Face (T.V k i)) (w₀ : T.V k i) (hw₀ : w₀ ∈ F.val)
    (v : T.V (k+1) i)
    (hv : v ∉ (T.faceClosure (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) F)).val)
    (b : T.V k i)
    (hbetw : (T.betw (k+1) i).between v (T.embed k i w₀) (T.embed k i b)) :
    b ∉ F.val := by
  intro hb
  apply hv
  set ccF := T.faceClosure (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) F)
  exact IsConvex_convClosure _ _ (face_sub_closure _ (Finset.mem_map_of_mem _ hw₀))
    _ (face_sub_closure _ (Finset.mem_map_of_mem _ hb)) v hbetw

lemma Dominates_convClosure_left (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).Dominates i σ A B) :
    (T.game k).Dominates i σ (T.faceClosure k i A) B := by
  intro a ha p hp b hb
  exact convClosure_pred A (fun v => ((T.game k).sign i p v b).nonneg)
    (fun v hv => h v hv p hp b hb)
    (fun v₁ v₂ c h₁ h₂ hc => T.playerConvex_left k i p v₁ v₂ c b hc h₁ h₂) ha

lemma Dominates_convClosure_right (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).Dominates i σ A B) :
    (T.game k).Dominates i σ A (T.faceClosure k i B) := by
  intro a ha p hp b hb
  exact convClosure_pred B (fun v => ((T.game k).sign i p a v).nonneg)
    (fun v hv => h a ha p hp v hv)
    (fun v₁ v₂ c h₁ h₂ hc => T.playerConvex_right k i p v₁ v₂ c a hc h₁ h₂) hb

/-- Dominates preserved when closing a single opponent j's face.
    Uses `opponentConvex` to interpolate over j's convex closure. -/
lemma Dominates_convClosure_opp (k : ℕ) {i : I} (j : I) (hj : j ≠ i)
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).Dominates i σ A B) :
    (T.game k).Dominates i (Function.update σ j (T.faceClosure k j (σ j))) A B := by
  intro a ha p hp b hb
  have hpj : p j ∈ (T.faceClosure k j (σ j)).val := by
    have := hp j hj; rwa [Function.update_self] at this
  have := @convClosure_pred _ _ _ (T.betw k j) (σ j)
    (fun v => ((T.game k).sign i (Function.update p j v) a b).nonneg) _
    (fun v hv => h a ha (Function.update p j v)
      (fun m hm => by
        by_cases hmj : m = j
        · subst hmj; simp [Function.update_self]; exact hv
        · rw [Function.update_of_ne hmj]
          have := hp m hm; rwa [Function.update_of_ne hmj] at this)
      b hb)
    (fun v₁ v₂ c hv₁ hv₂ hc => T.opponentConvex k i j hj
      (Function.update p j v₁) (Function.update p j v₂) a b
      (fun m hm => by simp [Function.update_of_ne hm])
      (Function.update p j c)
      (fun m hm => by simp [Function.update_of_ne hm])
      (by simp [Function.update_self]; exact hc)
      hv₁ hv₂)
    (v := p j) hpj
  simp only [Function.update_eq_self] at this; exact this

/-- Dominates preserved under convex closure of all players' faces.
    Closes opponents one at a time via `Finset.induction`, applying
    `Dominates_convClosure_opp` at each step (Fubini-style). -/
lemma Dominates_convexClosureProfile (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).Dominates i σ A B) :
    (T.game k).Dominates i (T.convexClosureProfile k σ) A B := by
  -- τ S = profile with opponents in S closed
  set τ : Finset I → Base.Profile I (T.V k) :=
    fun S j => if j ∈ S then T.faceClosure k j (σ j) else σ j
  suffices key : ∀ S : Finset I, (∀ j ∈ S, j ≠ i) →
      (T.game k).Dominates i (τ S) A B by
    have hfull := key (Finset.univ.filter (· ≠ i)) (fun j hj => by simp at hj; exact hj)
    -- convexClosureProfile differs from τ(univ \ {i}) only at i, which Dominates ignores
    intro a ha p hp b hb
    apply hfull a ha p _ b hb
    intro m hm
    have := hp m hm
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
    suffices h_eq : τ (insert j S') = Function.update (τ S') j (T.faceClosure k j ((τ S') j)) by
      rw [h_eq]; exact T.Dominates_convClosure_opp k j hjne base
    rw [hτj]; funext m
    by_cases hm : m = j
    · subst hm; simp [τ, hj, Function.update_self]
    · have := Function.update_of_ne hm (T.faceClosure k j (σ j)) (τ S')
      rw [this]; simp [τ, Finset.mem_insert, hm]

/-- Convex closure preserves Nash. A strict deviation from the closed profile
    would imply one from the original (by antitone + mono_right), contradiction. -/
lemma IsNash_convexClosureProfile (k : ℕ)
    {σ : Base.Profile I (T.V k)}
    (hN : (T.game k).IsNash σ) :
    (T.game k).IsNash (T.convexClosureProfile k σ) := by
  set τ := T.convexClosureProfile k σ
  intro i A hSD
  apply hN i A
  constructor
  · exact Dominates.antitone (T.game k) (fun j _ => face_sub_closure (σ j))
      (Dominates.mono_right (T.game k) (face_sub_closure (σ i)) hSD.1)
  · intro hback
    exact hSD.2 (T.Dominates_convexClosureProfile k (T.Dominates_convClosure_left k hback))

/-- Convex closure preserves OutsideDom. For v' outside and w' inside the closed face,
    domination extends from σ i to its closure via `playerConvex_left`. -/
lemma OutsideDom_convexClosureProfile (k : ℕ)
    {σ : Base.Profile I (T.V k)}
    (h_od : ∀ j, (T.game k).OutsideDom j σ) (i : I) :
    (T.game k).OutsideDom i (T.convexClosureProfile k σ) := by
  set τ := T.convexClosureProfile k σ
  intro v' hv' w' hw'
  have hv'_σ : v' ∉ (σ i).val := fun hv_mem => hv' (face_sub_closure (σ i) hv_mem)
  have h_ext : ∀ w₀ ∈ (σ i).val,
      (T.game k).Dominates i τ (Face.vertex w₀) (Face.vertex v') :=
    fun w₀ hw₀ => T.Dominates_convexClosureProfile k (h_od i v' hv'_σ w₀ hw₀)
  intro a ha p hp b hb
  simp [Face.vertex] at ha hb
  rw [ha, hb]
  exact convClosure_pred (σ i) (fun u => ((T.game k).sign i p u v').nonneg)
    (fun w₀ hw₀ => h_ext w₀ hw₀ w₀ (by simp [Face.vertex]) p hp v' (by simp [Face.vertex]))
    (fun v₁ v₂ c h₁ h₂ hc => T.playerConvex_left k i p v₁ v₂ c v' hc h₁ h₂) hw'

/-- Coherence transfers Dominates from coarse to fine level on embedded faces.
    Builds a coarse profile from preimages of opponents, applies `sign_irrel` to
    replace the fine profile with the embedded coarse one, then uses `coherent`. -/
lemma Dominates_embed (k : ℕ) {i : I}
    {σ : Base.Profile I (T.V k)} {A B : Face (T.V k i)}
    (h : (T.game k).Dominates i σ A B) :
    (T.game (k+1)).Dominates i
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

/-- **OD transfer across levels** — the main technical result.

    If OD holds at level k, it holds at level k+1 after embedding and convex closure.
    The proof has three steps for showing sign(p, w', v') ≥ 0 where w' is inside
    and v' is outside the closed embedded face:

    1. For embedded inside w₀ vs embedded outside v₀: use `Dominates_embed` + closure.
    2. For embedded inside w₀ vs arbitrary outside v': use `fine_between_embedded_at` to
       write v' between embed(w₀) and some embed(b₀), then `playerConvex_right`.
    3. For arbitrary inside w' vs v': extend from step 2 via `playerConvex_left` on
       the convex closure. -/
-- ANCHOR: outsideDom_embed_convClosure
theorem outsideDom_embed_convClosure (k : ℕ)
    {σ : Base.Profile I (T.V k)}
    (h_od : ∀ i, (T.game k).OutsideDom i σ)
    (i : I) :
    (T.game (k+1)).OutsideDom i
      (T.convexClosureProfile (k+1)
        (embedProfile
          (T.embed k) (T.embed_inj k) σ)) := by
-- ANCHOR_END: outsideDom_embed_convClosure
  set σ' := embedProfile (T.embed k) (T.embed_inj k) σ
  set σ'' := T.convexClosureProfile (k+1) σ'
  intro v' hv' w' hw' a ha p hp b hb
  simp [Face.vertex] at ha hb
  rw [ha, hb]
  -- Step 1: embedded inside vs embedded outside
  have step1 : ∀ w₀ ∈ (σ i).val, ∀ v₀ ∉ (σ i).val,
      ((T.game (k+1)).sign i p (T.embed k i w₀) (T.embed k i v₀)).nonneg := by
    intro w₀ hw₀ v₀ hv₀
    have h_dfle := T.Dominates_convexClosureProfile (k+1) (T.Dominates_embed k (h_od i v₀ hv₀ w₀ hw₀))
    exact h_dfle (T.embed k i w₀)
      (Finset.mem_map_of_mem _ (by simp [Face.vertex]))
      p hp (T.embed k i v₀)
      (Finset.mem_map_of_mem _ (by simp [Face.vertex]))
  -- Step 2: embedded inside vs arbitrary outside (uses fine_between_embedded_at)
  have step2 : ∀ w₀ ∈ (σ i).val,
      ((T.game (k+1)).sign i p (T.embed k i w₀) v').nonneg := by
    intro w₀ hw₀
    obtain ⟨b₀, hbetw⟩ := T.fine_between_embedded_at k i v' w₀
    have hb₀ : b₀ ∉ (σ i).val := T.outside_betw_witness_outside k i (σ i) w₀ hw₀ v' hv' b₀ hbetw
    have hrefl : ((T.game (k+1)).sign i p (T.embed k i w₀) (T.embed k i w₀)).nonneg := by
      rw [(T.game (k+1)).sign_refl]; exact Sign.nonneg_zero
    exact T.playerConvex_right (k+1) i p (T.embed k i w₀) (T.embed k i b₀) v'
      (T.embed k i w₀) hbetw hrefl (step1 w₀ hw₀ b₀ hb₀)
  -- Step 3: extend to full convex closure via playerConvex_left
  exact convClosure_pred (σ' i) (fun u => ((T.game (k+1)).sign i p u v').nonneg)
    (fun u hu => by
      simp only [σ', embedProfile, embedFace, Finset.mem_map, Function.Embedding.coeFn_mk] at hu
      obtain ⟨w₀, hw₀, rfl⟩ := hu
      exact step2 w₀ hw₀)
    (fun v₁ v₂ c h₁ h₂ hc => T.playerConvex_left (k+1) i p v₁ v₂ c v' hc h₁ h₂) hw'

-- ================================================================
-- Nash refinement
-- ================================================================

-- ANCHOR: FaceRefines
/-- F' refines F: F' ⊆ convClosure(embed(F)). -/
def FaceRefines (k : ℕ) (i : I)
    (F' : Face (T.V (k+1) i))
    (F : Face (T.V k i)) : Prop :=
  Face.IsSubface F'
    (T.faceClosure (k+1) i
      (embedFace (T.embed k i) (T.embed_inj k i) F))
-- ANCHOR_END: FaceRefines

-- ANCHOR: ProfileRefines
def ProfileRefines (k : ℕ)
    (σ' : Base.Profile I (T.V (k+1)))
    (σ : Base.Profile I (T.V k)) : Prop :=
  ∀ i, T.FaceRefines k i (σ' i) (σ i)
-- ANCHOR_END: ProfileRefines

-- ANCHOR: HasConvexFaces
def HasConvexFaces (k : ℕ)
    (σ : Base.Profile I (T.V k)) : Prop :=
  ∀ i, @IsConvex (T.V k i) (T.betw k i) (σ i).val
-- ANCHOR_END: HasConvexFaces

/-- At every level k, there exists a Nash equilibrium that is OD and convex-closed.
    Inductive step: embed level-k Nash into level k+1, convex-close, transfer OD
    via `outsideDom_embed_convClosure`, run descent, convex-close the result. -/
-- ANCHOR: nash_refining_sequence
theorem nash_refining_sequence (k : ℕ) :
    ∃ σ : Base.Profile I (T.V k),
      (T.game k).IsNash σ ∧
      (∀ i, (T.game k).OutsideDom i σ) ∧
      T.HasConvexFaces k σ := by
-- ANCHOR_END: nash_refining_sequence
  induction k with
  | zero =>
    have h_od_full : ∀ i, (T.game 0).OutsideDom i (fun _ => Face.full) :=
      fun i => OutsideDom.maximal (T.game 0) i
    obtain ⟨τ, hτN, _, hτ_od⟩ := (T.game 0).nash_exists_sub_of_outsideDom (fun _ => Face.full) h_od_full
    exact ⟨T.convexClosureProfile 0 τ,
      T.IsNash_convexClosureProfile 0 hτN,
      T.OutsideDom_convexClosureProfile 0 hτ_od,
      fun i => IsConvex_convClosure (τ i)⟩
  | succ n ih =>
    obtain ⟨σ_n, hN_n, hOD_n, _⟩ := ih
    set σ_cl := T.convexClosureProfile (n+1) (embedProfile (T.embed n) (T.embed_inj n) σ_n)
    have hOD_cl : ∀ i, (T.game (n+1)).OutsideDom i σ_cl :=
      T.outsideDom_embed_convClosure n hOD_n
    obtain ⟨τ, hτN, _, hτ_od⟩ := (T.game (n+1)).nash_exists_sub_of_outsideDom σ_cl hOD_cl
    exact ⟨T.convexClosureProfile (n+1) τ,
      T.IsNash_convexClosureProfile (n+1) hτN,
      T.OutsideDom_convexClosureProfile (n+1) hτ_od,
      fun i => IsConvex_convClosure (τ i)⟩

/-- Fine Nash refines coarse Nash: there exist Nash equilibria at levels k and k+1
    with the fine one contained in the convex closure of the embedded coarse one. -/
-- ANCHOR: nash_at_next_level_refines
theorem nash_at_next_level_refines (k : ℕ) :
    ∃ σ : Base.Profile I (T.V k),
    ∃ σ' : Base.Profile I (T.V (k+1)),
      (T.game k).IsNash σ ∧
      (T.game (k+1)).IsNash σ' ∧
      T.ProfileRefines k σ' σ := by
-- ANCHOR_END: nash_at_next_level_refines
  obtain ⟨σ_k, hN_k, hOD_k, _⟩ := T.nash_refining_sequence k
  set σ_cl := T.convexClosureProfile (k+1) (embedProfile (T.embed k) (T.embed_inj k) σ_k)
  have hOD_cl : ∀ i, (T.game (k+1)).OutsideDom i σ_cl :=
    T.outsideDom_embed_convClosure k hOD_k
  obtain ⟨τ, hτN, hτ_sub, hτ_od⟩ := (T.game (k+1)).nash_exists_sub_of_outsideDom σ_cl hOD_cl
  set τ' := T.convexClosureProfile (k+1) τ
  refine ⟨σ_k, τ', hN_k, T.IsNash_convexClosureProfile (k+1) hτN, fun i => ?_⟩
  -- faceClosure(τ i) ⊆ faceClosure(σ_cl i) = faceClosure(faceClosure(embed(σ_k i))) = faceClosure(embed(σ_k i))
  show Face.IsSubface (T.faceClosure (k+1) i (τ i))
    (T.faceClosure (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) (σ_k i)))
  have h1 : Face.IsSubface (τ i) (T.faceClosure (k+1) i (embedFace (T.embed k i) (T.embed_inj k i) (σ_k i))) :=
    hτ_sub i
  intro x hx
  have hx_cc := convClosure_mono h1 hx
  exact convClosure_sub_of_convex _ _ (fun y hy => hy)
    (IsConvex_convClosure _) hx_cc

end SignTower

end Refinement
