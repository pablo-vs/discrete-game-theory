import SyntheticGameTheory
import Mathlib.Algebra.Order.Ring.Nat

namespace SyntheticGameTheory

/-- At level k, a "grid action" for a player with vertex set V is a weight
    vector assigning each vertex a weight in {0, ..., 2^k}. This represents
    a dyadic approximation to a mixture over pure actions. -/
abbrev GridAction (V : Type*) (k : ℕ) := V → Fin (2^k + 1)

namespace GridAction

variable {V : Type*}

private lemma div_pow_lt (h : n < 2^j + 1) (hij : i ≤ j) :
    n / 2^(j - i) < 2^i + 1 := by
  have h1 : 0 < 2 ^ (j - i) := Nat.two_pow_pos _
  have h2 : n / 2^(j-i) ≤ 2^j / 2^(j-i) := Nat.div_le_div_right (by omega)
  rw [← Nat.pow_sub_mul_pow 2 hij] at h2
  simp [Nat.mul_div_cancel_left _ h1] at h2
  omega

/-- Projection from finer to coarser grid by integer division. -/
def proj (hij : i ≤ j) (c : GridAction V j) : GridAction V i :=
  fun v => ⟨(c v).val / 2^(j - i), div_pow_lt (c v).isLt hij⟩

instance instNonempty (k : ℕ) : Nonempty (GridAction V k) :=
  ⟨fun _ => 0⟩

theorem proj_refl (c : GridAction V k) :
    proj (le_refl k) c = c := by
  funext v; simp [proj]

theorem proj_trans (hij : i ≤ j) (hjk : j ≤ k) (c : GridAction V k) :
    proj hij (proj hjk c) = proj (hij.trans hjk) c := by
  funext v; simp [proj]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have : k - j + (j - i) = k - i := by omega
  rw [this]

theorem proj_finite_fibers [Fintype V] (a : GridAction V i) :
    {b : GridAction V (i + 1) | proj (Nat.le_succ i) b = a}.Finite :=
  Set.toFinite _

end GridAction

/-- A grid profile: each player picks a grid action at precision k. -/
abbrev GridProfile (N : Type*) (V : N → Type*) (k : ℕ) :=
  ∀ i : N, GridAction (V i) k

namespace GridProfile

variable {N : Type*} {V : N → Type*}

/-- Project a grid profile from level j to level i. -/
def proj (hij : i ≤ j) (σ : GridProfile N V j) : GridProfile N V i :=
  fun n => GridAction.proj hij (σ n)

theorem proj_refl (σ : GridProfile N V k) :
    proj (le_refl k) σ = σ := by
  funext n; exact GridAction.proj_refl _

theorem proj_trans (hij : i ≤ j) (hjk : j ≤ k) (σ : GridProfile N V k) :
    proj hij (proj hjk σ) = proj (hij.trans hjk) σ := by
  funext n; exact GridAction.proj_trans hij hjk _

end GridProfile

end SyntheticGameTheory
