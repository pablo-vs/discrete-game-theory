import SyntheticGameTheory.Basic

namespace SyntheticGameTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {V : N → Type*} [∀ i, DecidableEq (V i)] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]

namespace Game

variable (G : Game N V)

-- ================================================================
-- Section 1: Pure Nash Equilibria
-- ================================================================

/-- A pure profile is a pure Nash equilibrium if no player can strictly
    improve by unilaterally deviating to a different action. -/
def IsPureNash (p : PureProfile N V) : Prop :=
  ∀ i : N, ∀ v : V i, G.pref i p (Function.update p i v)

-- ================================================================
-- Section 2: Pareto Dominance and Frontier
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
-- Section 3: Pure Nash Properties
-- ================================================================

omit [Fintype N] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)] in
/-- A pure profile is Nash iff no player has a strict unilateral improvement. -/
theorem isPureNash_iff (p : PureProfile N V) :
    G.IsPureNash p ↔ ∀ i, ∀ v : V i, G.pref i p (Function.update p i v) :=
  Iff.rfl

-- ================================================================
-- Section 4: Pareto Theorems
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
