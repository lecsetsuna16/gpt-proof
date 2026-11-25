import ChainModel
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary inverse-square core bounds

The estimates below use a telescoping majorant, not an approximation to an
infinite sum. The collision statement is an explicit epsilon-style proof that
a positive inverse-square core dominates the bounded Cauchy interaction.
-/

namespace VerifiedChain

open scoped BigOperators

theorem inverse_sq_step {x : ℝ} (hx : 1 ≤ x) :
    1 / x ^ 2 ≤ 2 / x - 2 / (x + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx1 : 0 < x + 1 := by linarith
  calc
    1 / x ^ 2 ≤ 2 / (x * (x + 1)) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hx0) (mul_pos hx0 hx1)).2
      nlinarith
    _ = 2 / x - 2 / (x + 1) := by
      field_simp
      ring

theorem inverse_sq_partial_bound (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ 2) ≤
      2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hn : 1 ≤ (N : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hs := inverse_sq_step hn
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

theorem inverse_sq_partial_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  have h := inverse_sq_partial_bound N
  have hp : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
  linarith

theorem inverse_sq_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  apply summable_of_sum_range_le (c := 2)
  · intro n
    positivity
  · exact inverse_sq_partial_le_two

theorem inverse_sq_tsum_le_two :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · exact inverse_sq_partial_le_two

theorem invSq_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := inverse_sq_summable

theorem invSq_tsum_le_two :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := inverse_sq_tsum_le_two

theorem bounded_core_summable (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha8 : ∀ n, a n ≤ 8) :
    Summable (fun n : ℕ => a n / ((n : ℝ) + 1) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (ha0 n) (sq_nonneg _))
    (fun n => ?_)
    (inverse_sq_summable.mul_left 8)
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right (ha8 n) (sq_nonneg ((n : ℝ) + 1))

theorem bounded_core_nonneg (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) :
    0 ≤ ∑' n : ℕ, a n / ((n : ℝ) + 1) ^ 2 :=
  tsum_nonneg fun n => div_nonneg (ha0 n) (sq_nonneg _)

theorem bounded_core_le_sixteen (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha8 : ∀ n, a n ≤ 8) :
    (∑' n : ℕ, a n / ((n : ℝ) + 1) ^ 2) ≤ 16 := by
  calc
    (∑' n : ℕ, a n / ((n : ℝ) + 1) ^ 2)
        ≤ ∑' n : ℕ, 8 * (1 / ((n : ℝ) + 1) ^ 2) := by
      apply (bounded_core_summable a ha0 ha8).tsum_le_tsum
        (fun n => ?_) (inverse_sq_summable.mul_left 8)
      simpa only [mul_one_div] using
        div_le_div_of_nonneg_right (ha8 n) (sq_nonneg ((n : ℝ) + 1))
    _ = 8 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) := tsum_mul_left
    _ ≤ 16 := by nlinarith [inverse_sq_tsum_le_two]

theorem uniform_core_summable :
    Summable (fun n : ℕ =>
      (unsignedShell uniform (residue (n + 1)) : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  apply bounded_core_summable
  · intro n
    exact_mod_cast (uniform_unsigned_bounds (residue (n + 1))).1
  · intro n
    exact_mod_cast (uniform_unsigned_bounds (residue (n + 1))).2

theorem shifted_core_summable :
    Summable (fun n : ℕ =>
      (unsignedShell shifted (residue (n + 1)) : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  apply bounded_core_summable
  · intro n
    exact_mod_cast (shifted_unsigned_bounds (residue (n + 1))).1
  · intro n
    exact_mod_cast (shifted_unsigned_bounds (residue (n + 1))).2

theorem coreEnergy_uniform_nonneg : 0 ≤ coreEnergy uniform := by
  apply bounded_core_nonneg
  intro n
  exact_mod_cast (uniform_unsigned_bounds (residue (n + 1))).1

theorem coreEnergy_shifted_nonneg : 0 ≤ coreEnergy shifted := by
  apply bounded_core_nonneg
  intro n
  exact_mod_cast (shifted_unsigned_bounds (residue (n + 1))).1

theorem coreEnergy_shifted_le_sixteen : coreEnergy shifted ≤ 16 := by
  apply bounded_core_le_sixteen
  · intro n
    exact_mod_cast (shifted_unsigned_bounds (residue (n + 1))).1
  · intro n
    exact_mod_cast (shifted_unsigned_bounds (residue (n + 1))).2

theorem core_minus_soft_lower_bound (lambda s r : ℝ) (hs : |s| ≤ 1) :
    lambda / r ^ 2 - 1 ≤ lambda / r ^ 2 - s * (4 / (4 + r ^ 2)) := by
  have hd : 0 < 4 + r ^ 2 := by nlinarith [sq_nonneg r]
  have hf0 : 0 ≤ (4 : ℝ) / (4 + r ^ 2) := by positivity
  have hf1 : (4 : ℝ) / (4 + r ^ 2) ≤ 1 := by
    apply (div_le_one hd).2
    nlinarith [sq_nonneg r]
  have hs1 : s ≤ 1 := le_trans (le_abs_self s) hs
  have hprod : s * (4 / (4 + r ^ 2)) ≤ 1 := by
    calc
      s * (4 / (4 + r ^ 2)) ≤ 1 * (4 / (4 + r ^ 2)) :=
        mul_le_mul_of_nonneg_right hs1 hf0
      _ ≤ 1 := by simpa using hf1
  linarith

/-- For every requested energy height, a sufficiently small positive separation
has greater pair energy. This proves the hard repulsive collision barrier for
every positive core coefficient and both species-sign choices. -/
theorem collision_barrier (lambda : ℝ) (hlambda : 0 < lambda)
    (s : ℝ) (hs : |s| ≤ 1) (B : ℝ) (hB : 0 ≤ B) :
    ∃ delta > 0, ∀ r : ℝ, 0 < r → r < delta →
      B < lambda / r ^ 2 - s * (4 / (4 + r ^ 2)) := by
  let delta : ℝ := min 1 (lambda / (B + 1))
  have hden : 0 < B + 1 := by linarith
  have hdelta : 0 < delta := lt_min zero_lt_one (div_pos hlambda hden)
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hrd
  have hr1 : r < 1 := lt_of_lt_of_le hrd (min_le_left _ _)
  have hrl : r < lambda / (B + 1) := lt_of_lt_of_le hrd (min_le_right _ _)
  have hrprod : r * (B + 1) < lambda := (lt_div_iff₀ hden).1 hrl
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hprod2 : (B + 1) * r ^ 2 < lambda := by
    calc
      (B + 1) * r ^ 2 ≤ (B + 1) * r := mul_le_mul_of_nonneg_left hr2 hden.le
      _ < lambda := by simpa [mul_comm] using hrprod
  have hinv : B + 1 < lambda / r ^ 2 := (lt_div_iff₀ (sq_pos_of_pos hr)).2 hprod2
  have hbound := core_minus_soft_lower_bound lambda s r hs
  linarith

#print axioms inverse_sq_tsum_le_two
#print axioms bounded_core_le_sixteen
#print axioms coreEnergy_shifted_le_sixteen
#print axioms collision_barrier

end VerifiedChain
