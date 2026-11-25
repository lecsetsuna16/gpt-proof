import CoreBounds
import PolynomialCertificate
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
The infinite Cauchy interaction is certified by an eight-term block identity
and a convergent inverse-square majorant. Numerical experiments do not enter
any theorem below.
-/

noncomputable section

namespace VerifiedChain

open scoped BigOperators

def cauchyProfile (n : ℕ) : ℝ := 16 / (16 + (n : ℝ)^2)

def gapCoefficient (r : ℕ) : ℝ :=
  if r = 2 ∨ r = 6 then 5/2 else if r = 0 then 0 else -1

def gapTerm (n : ℕ) : ℝ :=
  gapCoefficient ((n+1)%8) * cauchyProfile (n+1)

theorem cauchyProfile_nonneg (n : ℕ) : 0 ≤ cauchyProfile n := by
  unfold cauchyProfile
  positivity

theorem cauchyProfile_succ_bound (n : ℕ) :
    cauchyProfile (n+1) ≤ 16 * (1 / ((n : ℝ)+1)^2) := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  dsimp [cauchyProfile]
  push_cast
  rw [mul_one_div]
  apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hn)
  nlinarith [sq_nonneg ((n : ℝ)+1)]

theorem bounded_cauchy_summable (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C) :
    Summable (fun n : ℕ => a n * cauchyProfile (n+1)) := by
  apply Summable.of_norm_bounded (invSq_summable.mul_left (C*16))
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cauchyProfile_nonneg _)]
  calc
    |a n| * cauchyProfile (n+1) ≤ C * cauchyProfile (n+1) :=
      mul_le_mul_of_nonneg_right (ha n) (cauchyProfile_nonneg _)
    _ ≤ C * (16 * (1 / ((n : ℝ)+1)^2)) :=
      mul_le_mul_of_nonneg_left (cauchyProfile_succ_bound n) hC
    _ = (C*16) * (1 / ((n : ℝ)+1)^2) := by ring

theorem gapCoefficient_abs_bound (r : ℕ) : |gapCoefficient r| ≤ 3 := by
  unfold gapCoefficient
  split_ifs <;> norm_num

theorem gapTerm_summable : Summable gapTerm := by
  exact bounded_cauchy_summable
    (fun n => gapCoefficient ((n+1)%8)) 3 (by norm_num)
    (fun n => gapCoefficient_abs_bound _)

set_option maxRecDepth 4000 in
theorem block_is_eight_terms (m : ℕ) :
    (∑ r : Fin 8, gapTerm (m*8+r.val)) = cauchyBlock (m : ℝ) := by
  norm_num [Fin.sum_univ_succ, gapTerm, gapCoefficient, cauchyProfile,
    Nat.add_mod, Nat.mul_mod, cauchyBlock]
  ring

theorem blocked_summable : Summable (fun m : ℕ => cauchyBlock (m : ℝ)) := by
  have hp : Summable (fun p : ℕ × Fin 8 => gapTerm (p.1*8+p.2.val)) :=
    (Nat.divModEquiv 8).symm.summable_iff.mpr gapTerm_summable
  exact hp.prod.congr (fun m => by
    rw [tsum_fintype]
    exact block_is_eight_terms m)

theorem regroup_gap :
    (∑' n : ℕ, gapTerm n) = ∑' m : ℕ, cauchyBlock (m : ℝ) := by
  have hp : Summable (fun p : ℕ × Fin 8 => gapTerm (p.1*8+p.2.val)) :=
    (Nat.divModEquiv 8).symm.summable_iff.mpr gapTerm_summable
  calc
    (∑' n : ℕ, gapTerm n) = ∑' p : ℕ × Fin 8, gapTerm (p.1*8+p.2.val) :=
      ((Nat.divModEquiv 8).symm.tsum_eq gapTerm).symm
    _ = ∑' m : ℕ, ∑' r : Fin 8, gapTerm (m*8+r.val) := hp.tsum_prod
    _ = ∑' m : ℕ, cauchyBlock (m : ℝ) := by
      apply tsum_congr
      intro m
      rw [tsum_fintype]
      exact block_is_eight_terms m

theorem cauchy_block_tail_summable :
    Summable (fun n : ℕ => cauchyBlock ((n : ℝ)+1)) := by
  simpa using (summable_nat_add_iff 1).mpr blocked_summable

theorem cauchy_tail_lower :
    -(1/400 : ℝ) ≤ ∑' n : ℕ, cauchyBlock ((n : ℝ)+1) := by
  have hc :
      (∑' n : ℕ, -(1/800 : ℝ) * (1 / ((n : ℝ)+1)^2)) ≤
        ∑' n : ℕ, cauchyBlock ((n : ℝ)+1) := by
    apply (invSq_summable.mul_left (-(1/800 : ℝ))).tsum_le_tsum
      (fun n => ?_) cauchy_block_tail_summable
    have hn : 1 ≤ (n : ℝ)+1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    convert cauchy_block_tail_bound ((n : ℝ)+1) hn using 1
    simp only [one_div, mul_inv_rev]
    ring
  rw [tsum_mul_left] at hc
  nlinarith [invSq_tsum_le_two]

theorem cauchy_gap_series_lower :
    (49/1000 : ℝ) < ∑' n : ℕ, gapTerm n := by
  rw [regroup_gap]
  have hsplit : cauchyBlock 0 + (∑' n : ℕ, cauchyBlock ((n : ℝ)+1)) =
      ∑' n : ℕ, cauchyBlock (n : ℝ) := by
    simpa using blocked_summable.sum_add_tsum_nat_add 1
  linarith [first_block_lower, cauchy_tail_lower]

#print axioms cauchy_gap_series_lower

end VerifiedChain
