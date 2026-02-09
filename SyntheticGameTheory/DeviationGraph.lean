import SyntheticGameTheory
import Mathlib.Logic.Relation

namespace SyntheticGameTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]

namespace Game

variable (G : Game N V)

-- ================================================================
-- Section 1: Pure Nash and Unilateral Deviations
-- ================================================================

/-- A pure profile is a pure Nash equilibrium if no player can strictly
    improve by unilaterally deviating to a different action. -/
def IsPureNash (p : PureProfile N V) : Prop :=
  ∀ i : N, ∀ v : V i, G.pref i p (Function.update p i v)

/-- Unilateral deviation: p → q where exactly one player deviates and
    strictly prefers q. Since pref is total, ¬pref i p q means q is
    strictly better for i. -/
def UniDev (p q : PureProfile N V) : Prop :=
  ∃ i : N, (∀ j : N, j ≠ i → p j = q j) ∧ ¬G.pref i p q

-- ================================================================
-- Section 2: Game Classification
-- ================================================================

/-- A game is cooperative if its unilateral deviation graph is acyclic.
    This generalizes the notion of ordinal potential games. -/
def IsCooperative : Prop :=
  ∀ p : PureProfile N V, ¬Relation.TransGen G.UniDev p p

/-- A game is competitive if every pure profile lies on a cycle. -/
def IsCompetitive : Prop :=
  ∀ p : PureProfile N V, ∃ q, G.UniDev p q ∧ Relation.TransGen G.UniDev q p

-- ================================================================
-- Section 3: Pareto Dominance and Frontier
-- ================================================================

/-- Profile p weakly Pareto-dominates q: every player weakly prefers p to q. -/
def WeakPareto (p q : PureProfile N V) : Prop :=
  ∀ i : N, G.pref i p q

/-- Profile p strictly Pareto-dominates q: every player weakly prefers p,
    and at least one player strictly prefers p. -/
def StrictPareto (p q : PureProfile N V) : Prop :=
  G.WeakPareto p q ∧ ∃ i : N, ¬G.pref i q p

/-- A pure profile is Pareto-optimal if no other profile strictly
    Pareto-dominates it. -/
def IsParetoOptimal (p : PureProfile N V) : Prop :=
  ∀ q : PureProfile N V, ¬G.StrictPareto q p

-- ================================================================
-- Section 4: Core Theorems — Deviations
-- ================================================================

omit [Fintype N] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] in
/-- Pure Nash is equivalent to having no unilateral deviations. -/
theorem pureNash_iff_no_unidev (p : PureProfile N V) :
    G.IsPureNash p ↔ ∀ q, ¬G.UniDev p q := by
  constructor
  · intro hNash q ⟨i, huniq, hpref⟩
    have huniq' : q = Function.update p i (q i) := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h, huniq j h]
    rw [huniq'] at hpref
    exact hpref (hNash i (q i))
  · intro hNoDev i v
    by_contra hNot
    exact hNoDev _ ⟨i, fun j hji => by simp [hji], hNot⟩

omit [∀ i, Nonempty (V i)] in
/-- A cooperative game has a well-founded reversed transitive closure. -/
theorem cooperative_iff_wellFounded :
    G.IsCooperative ↔ WellFounded (fun p q => Relation.TransGen G.UniDev q p) := by
  constructor
  · intro hCoop
    haveI : Std.Irrefl (fun p q : PureProfile N V => Relation.TransGen G.UniDev q p) :=
      ⟨fun p hp => hCoop p hp⟩
    haveI : IsTrans (PureProfile N V) (fun p q => Relation.TransGen G.UniDev q p) :=
      ⟨fun _ _ _ hqp hrq => Relation.TransGen.trans hrq hqp⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  · intro hWF p hCycle
    exact hWF.irrefl.irrefl p hCycle

/-- Every cooperative game has at least one pure Nash equilibrium. -/
theorem cooperative_has_pureNash :
    G.IsCooperative → ∃ p, G.IsPureNash p := by
  intro hCoop
  rw [cooperative_iff_wellFounded] at hCoop
  classical
  obtain ⟨p, -, hp⟩ := hCoop.has_min Set.univ ⟨fun i => Classical.ofNonempty, trivial⟩
  exact ⟨p, (pureNash_iff_no_unidev G p).mpr fun q hDev => hp q trivial (.single hDev)⟩

omit [Fintype N] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] in
/-- Competitive games have no pure Nash equilibria. -/
theorem competitive_no_pureNash :
    G.IsCompetitive → ¬∃ p, G.IsPureNash p := by
  intro hComp ⟨p, hNash⟩
  obtain ⟨q, hDev, _⟩ := hComp p
  exact ((pureNash_iff_no_unidev G p).mp hNash) q hDev

-- ================================================================
-- Section 5: Core Theorems — Pareto
-- ================================================================

omit [Fintype N] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] in
/-- StrictPareto is irreflexive. -/
theorem strictPareto_irrefl (p : PureProfile N V) : ¬G.StrictPareto p p :=
  fun ⟨_, i, hni⟩ => hni ((G.pref_preorder i).refl p)

omit [Fintype N] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] in
/-- StrictPareto is transitive. -/
theorem strictPareto_trans {p q r : PureProfile N V} :
    G.StrictPareto p q → G.StrictPareto q r → G.StrictPareto p r := by
  intro ⟨hwpq, i, hiq⟩ ⟨hwqr, _, _⟩
  refine ⟨fun j => (G.pref_preorder j).toIsTrans.trans _ _ _ (hwpq j) (hwqr j), i, ?_⟩
  intro hrp
  exact hiq ((G.pref_preorder i).toIsTrans.trans _ _ _ (hwqr i) hrp)

/-- A Pareto-optimal profile always exists. -/
theorem exists_paretoOptimal : ∃ p : PureProfile N V, G.IsParetoOptimal p := by
  classical
  haveI : Std.Irrefl G.StrictPareto := ⟨G.strictPareto_irrefl⟩
  haveI : IsTrans _ G.StrictPareto :=
    ⟨fun _ _ _ => G.strictPareto_trans⟩
  have hWF : WellFounded G.StrictPareto :=
    Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨p, -, hp⟩ := hWF.has_min Set.univ ⟨fun i => Classical.ofNonempty, trivial⟩
  exact ⟨p, fun q hqp => hp q trivial hqp⟩

omit [Fintype N] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] in
/-- WeakPareto is reflexive. -/
theorem weakPareto_refl (p : PureProfile N V) : G.WeakPareto p p :=
  fun i => (G.pref_preorder i).refl p

omit [Fintype N] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] in
/-- WeakPareto is transitive. -/
theorem weakPareto_trans {p q r : PureProfile N V} :
    G.WeakPareto p q → G.WeakPareto q r → G.WeakPareto p r :=
  fun hpq hqr i => (G.pref_preorder i).toIsTrans.trans _ _ _ (hpq i) (hqr i)

end Game

end SyntheticGameTheory
