import tactic
import data.real.basic
import topology.metric_space.basic
import topology.uniform_space.cauchy
-- import analysis.specific_limits.basic

namespace my_stuff
open my_stuff

def cauchy_seq {X : Type*} [metric_space X] (a : ℕ → X) : Prop :=
∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → dist (a m) (a n) < ε

/- complete metric space for sequences -/
class complete_metric_space (X : Type)
  extends metric_space X := 
(cauchy_seq_converges : ∀ (f : ℕ → X), (cauchy_seq f) → (∃ (x : X), ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → has_dist.dist (f n) x < ε)))

/- contraction mapping definition -/
@[ext] structure contraction_mapping (X : Type) [metric_space X] :=
(T : X → X)
(contr : ∃ (q : ℝ), 0 ≤ q ∧ q < 1 ∧ ∀ (x y : X), has_dist.dist (T x) (T y) ≤ q * has_dist.dist x y)

instance {X : Type} [metric_space X] : has_coe_to_fun (contraction_mapping X) (λ _, X → X) :=
{ coe := contraction_mapping.T }

def contraction_sequence {X : Type} (T : X → X) (a : X) : ℕ → X
| 0 := a
| (n + 1) := T (contraction_sequence n)

def sequence_tendsto {X : Type*} [complete_metric_space X] (a : ℕ → X) (t : X) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (a n) t < ε

lemma contraction_sequence_cauchy {X : Type} [metric_space X] (T : contraction_mapping X) (a : X) :
  cauchy_seq (contraction_sequence T a) :=
begin
  /-
  dist (contraction_sequence T a m) (contraction_sequence T a n)
    ≤ ∑ i in range (m - n), dist (contraction_sequence T a (n + i)) (contraction_sequence T a (n + i + 1))
    ≤ ∑ i in range (m - n), q^i * dist (contraction_sequence T a n) (contraction_sequence T a (n + 1))
    ≤ ∑ i in range (m - n), q^i * δ
    ≤ (1 - q^(m - n)) / (1 - q) * δ
    < δ,
  -/
  unfold cauchy_seq,
  intros ε ε_pos,
  rcases T.contr with ⟨q, hq1, hq2, hq3⟩,
  -- q^N * dist (contraction_sequence T a N) a < ε
  sorry,
end

lemma contraction_sequence_converges {X : Type} [complete_metric_space X] (T : contraction_mapping X) (a : X) :
  ∃ (x : X), sequence_tendsto (contraction_sequence T a) x :=
begin
  apply complete_metric_space.cauchy_seq_converges,
  apply contraction_sequence_cauchy,
end

lemma nonneg_lt_all_zero {X : Type} [metric_space X] (a b : X) : (∀ ε > 0, dist a b < ε) → a = b :=
begin
  intro h,
  have h' : dist a b ≤ 0,
  {
    apply le_of_forall_le_of_dense,
    intros ε ε_pos,
    specialize h ε ε_pos,
    linarith,
  },
  have h'' : dist a b = 0,
  {
    exact le_antisymm h' dist_nonneg,
  },
  exact dist_eq_zero.mp h'',
end


-- Vas edits:
lemma helper1 {X : Type} [metric_space X] (T : contraction_mapping X) (a : X) : (T a = T.T a) := rfl
@[simp] lemma helper2 {X : Type} [metric_space X] (T : contraction_mapping X) (a : X) (n : ℕ) : contraction_sequence T a (n+1) = T (contraction_sequence T a n) := rfl

lemma contraction_mapping_contracts (X : Type) [hX : metric_space X] (T : contraction_mapping X) (a b : X) : dist (T a) (T b) ≤ dist a b := 
begin
  rcases T.contr with ⟨q, hq1, hq2, hq3⟩,
  specialize hq3 a b,
  have hq4 : q ≤ 1 := by linarith,
  have hcd : dist a b ≥ 0 := dist_nonneg,
  rw helper1,
  rw helper1,
  linarith [mul_le_of_le_one_left hcd hq4],
end

theorem banach_fixed_point (X : Type) [complete_metric_space X] (T : contraction_mapping X) (a : X) : ∃ (x : X), T x = x :=
begin
  rcases contraction_sequence_converges T a with ⟨x, hx⟩,
  use x,

  have H : ∀ ε, ε > 0 → dist (T x) x < ε,
  {
    intros ε hε,
    unfold sequence_tendsto at hx,

    have hε' : ε/2 > 0, {exact half_pos hε,},

    rcases hx (ε/2) hε' with ⟨N, hN⟩,
    
    have h0 : dist (T x) x ≤ dist (T x) (contraction_sequence T a (N+1)) + dist (contraction_sequence T a (N+1)) x,
    { exact dist_triangle (T x) (contraction_sequence T a (N+1)) x },
    have h1 : dist (T x) (contraction_sequence T a (N+1)) < ε/2, {
      specialize hN N nat.less_than_or_equal.refl,
      rw dist_comm,
      simp,
      linarith [contraction_mapping_contracts X T (contraction_sequence T a N) x, hN],
    },
    have h2 : dist (contraction_sequence T a (N+1)) x < ε/2, {
      exact hN (N+1) (by linarith),
    },

    calc dist (T x) x ≤ dist (T x) (contraction_sequence T a (N+1)) + dist (contraction_sequence T a (N+1)) x : h0
      ... < dist (T x) (contraction_sequence T a (N+1)) + ε/2 : by linarith [h2]
      ... < ε/2 + ε/2 : by linarith [h1]
      ... = ε : by linarith
  },
  
  apply nonneg_lt_all_zero,
  intros ε h',
  exact H ε h',
end


end my_stuff