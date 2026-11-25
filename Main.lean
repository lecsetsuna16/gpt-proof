import CauchyCertificate

/-!
# Repulsion at contact does not force uniform spacing

This is a self-contained counterexample within an explicitly specified binary
particle-chain model. The theorem does not assert the discovery of a new
literature conjecture or identify the global ground state.
-/

noncomputable section

namespace VerifiedChain

open scoped BigOperators

theorem uniform_signed_bound (r : Fin 8) :
    |(signedShell uniform r : ℝ)| ≤ 8 := by
  rw [uniform_signed_counts]
  fin_cases r <;> norm_num [uniformSigned]

theorem shifted_signed_bound (r : Fin 8) :
    |(signedShell shifted r : ℝ)| ≤ 8 := by
  rw [shifted_signed_counts]
  fin_cases r <;> norm_num [shiftedSigned]

theorem uniform_cauchy_summable :
    Summable (fun n : ℕ => (signedShell uniform (residue (n+1)) : ℝ) *
      cauchyProfile (n+1)) :=
  bounded_cauchy_summable _ 8 (by norm_num) (fun n => uniform_signed_bound _)

theorem shifted_cauchy_summable :
    Summable (fun n : ℕ => (signedShell shifted (residue (n+1)) : ℝ) *
      cauchyProfile (n+1)) :=
  bounded_cauchy_summable _ 8 (by norm_num) (fun n => shifted_signed_bound _)

theorem signed_gap_coefficient (r : Fin 8) :
    -(1/4 : ℝ) * ((signedShell uniform r : ℝ) - (signedShell shifted r : ℝ)) =
      gapCoefficient r.val := by
  rw [uniform_signed_counts, shifted_signed_counts]
  fin_cases r <;> norm_num [uniformSigned, shiftedSigned, gapCoefficient]

theorem cauchy_energy_gap_eq_series :
    signedEnergy uniform cauchyProfile - signedEnergy shifted cauchyProfile =
      ∑' n : ℕ, gapTerm n := by
  unfold signedEnergy
  rw [← mul_sub, ← uniform_cauchy_summable.tsum_sub shifted_cauchy_summable,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← sub_mul, ← mul_assoc, signed_gap_coefficient]
  rfl

theorem cauchy_energy_gap_lower :
    (49/1000 : ℝ) <
      signedEnergy uniform cauchyProfile - signedEnergy shifted cauchyProfile := by
  rw [cauchy_energy_gap_eq_series]
  exact cauchy_gap_series_lower

/-- Infinite shell energy, with the same all-pair repulsive core for both
species. Each ordered pair is counted, as in the source article's convention. -/
def totalEnergy (lambda : ℝ) (p : Cell) : ℝ :=
  signedEnergy p cauchyProfile + lambda * coreEnergy p

theorem strict_energy_gap (lambda : ℝ) (hlow : 0 ≤ lambda)
    (hhigh : lambda ≤ 1/1000) :
    (1/32 : ℝ) < totalEnergy lambda uniform - totalEnergy lambda shifted := by
  have hU : 0 ≤ lambda * coreEnergy uniform :=
    mul_nonneg hlow coreEnergy_uniform_nonneg
  have hX : lambda * coreEnergy shifted ≤ 16/1000 := by
    calc
      lambda * coreEnergy shifted ≤ lambda * 16 :=
        mul_le_mul_of_nonneg_left coreEnergy_shifted_le_sixteen hlow
      _ ≤ 16/1000 := by nlinarith
  unfold totalEnergy
  linarith [cauchy_energy_gap_lower]

theorem cauchy_profile_summable : Summable (fun n : ℕ => cauchyProfile (n+1)) := by
  simpa using bounded_cauchy_summable (fun _ => 1) 1 (by norm_num) (by norm_num)

theorem core_profile_summable : Summable (fun n : ℕ => (4 : ℝ)/(n+1 : ℝ)^2) := by
  simpa only [mul_one_div] using invSq_summable.mul_left 4

theorem natAbs_sq_cast (d : ℤ) : ((d.natAbs : ℕ) : ℝ)^2 = (d : ℝ)^2 := by
  simp only [Nat.cast_natAbs, Int.cast_abs, sq_abs]

theorem cauchy_profile_is_physical (d : ℤ) :
    cauchyProfile d.natAbs = (4 : ℝ)/(4+((d : ℝ)/2)^2) := by
  unfold cauchyProfile
  rw [natAbs_sq_cast]
  have hd : 0 < 16 + (d : ℝ)^2 := by positivity
  have he : 0 < 4 + ((d : ℝ)/2)^2 := by positivity
  field_simp
  ring

theorem core_profile_is_physical (d : ℤ) :
    (4 : ℝ)/(d.natAbs : ℝ)^2 = (1 : ℝ)/((d : ℝ)/2)^2 := by
  rw [natAbs_sq_cast]
  simp only [div_pow]
  norm_num

/-- Ordinary real-coordinate energy of the complete infinite chain. The
literal pair sums exclude exactly i=j,m=0 and include every other m : ℤ. -/
def physicalEnergy (lambda : ℝ) (p : Cell) : ℝ :=
  (1/4 : ℝ) * (
    lambda * literalPairSum p (fun _ _ => 1) (fun r => 1/r^2) -
    literalPairSum p (fun i j => ((charge i * charge j : ℤ) : ℝ))
      (fun r => 4/(4+r^2)))

theorem physicalEnergy_eq_totalEnergy (lambda : ℝ) (p : Cell) (hp : ordered p) :
    physicalEnergy lambda p = totalEnergy lambda p := by
  unfold totalEnergy physicalEnergy
  rw [signedEnergy_eq_imageSum p cauchyProfile cauchy_profile_summable,
    coreEnergy_eq_imageSum p core_profile_summable,
    imageSum_eq_literalPairSum p hp _ _ (fun r => 4/(4+r^2)) cauchy_profile_is_physical,
    imageSum_eq_literalPairSum p hp _ _ (fun r => 1/r^2) core_profile_is_physical]
  ring

/-- Main theorem, stated in the ordinary all-images physical energy. -/
theorem physical_counterexample (lambda : ℝ) (hlow : 0 ≤ lambda)
    (hhigh : lambda ≤ 1/1000) :
    (ordered uniform ∧ uniform 0 = 0) ∧
    (ordered shifted ∧ shifted 0 = 0) ∧
    (1/32 : ℝ) < physicalEnergy lambda uniform - physicalEnergy lambda shifted := by
  refine ⟨uniform_admissible, shifted_admissible, ?_⟩
  rw [physicalEnergy_eq_totalEnergy lambda uniform uniform_admissible.1,
    physicalEnergy_eq_totalEnergy lambda shifted shifted_admissible.1]
  exact strict_energy_gap lambda hlow hhigh

/-- A closed theorem with no user-supplied mathematical hypotheses. -/
theorem explicit_repulsive_core_counterexample :
    (1/32 : ℝ) <
      physicalEnergy (1/1000) uniform - physicalEnergy (1/1000) shifted :=
  (physical_counterexample (1/1000) (by norm_num) (by norm_num)).2.2

/-- `s` is the product of the two species labels, hence is either +1 or -1.
The value at r=0 is never included in a physical energy sum. -/
def pairPotential (lambda s r : ℝ) : ℝ :=
  lambda/r^2 - s*(4/(4+r^2))

/-- The single combined-potential formula for every ordered pair and every
integer translate of the cell. Only the central self-interaction is omitted. -/
def directEnergy (lambda : ℝ) (p : Cell) : ℝ :=
  (1/4 : ℝ) * ∑ i : Fin 4, ∑ j : Fin 4, ∑' m : ℤ,
    if i = j ∧ m = 0 then 0 else
      pairPotential lambda ((charge i * charge j : ℤ) : ℝ)
        (coordinate p j + 4*(m : ℝ) - coordinate p i)

set_option maxHeartbeats 2000000 in
theorem directEnergy_eq_physicalEnergy (lambda : ℝ) (p : Cell) (hp : ordered p) :
    directEnergy lambda p = physicalEnergy lambda p := by
  unfold directEnergy physicalEnergy literalPairSum
  congr 1
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hc := literal_images_summable p hp (fun _ _ => 1)
    (fun n => (4 : ℝ)/(n : ℝ)^2) (fun r => (1 : ℝ)/r^2)
    (by simpa only [Nat.cast_add, Nat.cast_one] using core_profile_summable)
    core_profile_is_physical i j
  have hs := literal_images_summable p hp
    (fun i j => ((charge i * charge j : ℤ) : ℝ))
    cauchyProfile (fun r => (4 : ℝ)/(4+r^2))
    cauchy_profile_summable cauchy_profile_is_physical i j
  rw [← tsum_mul_left, ← (hc.mul_left lambda).tsum_sub hs]
  apply tsum_congr
  intro m
  by_cases h : i = j ∧ m = 0
  · simp [h]
  · simp only [h, if_false, pairPotential, one_mul]
    ring

theorem direct_counterexample (lambda : ℝ) (hlow : 0 ≤ lambda)
    (hhigh : lambda ≤ 1/1000) :
    (1/32 : ℝ) < directEnergy lambda uniform - directEnergy lambda shifted := by
  rw [directEnergy_eq_physicalEnergy lambda uniform uniform_admissible.1,
    directEnergy_eq_physicalEnergy lambda shifted shifted_admissible.1]
  exact (physical_counterexample lambda hlow hhigh).2.2

/-- Closed headline theorem in the literal combined-potential energy. -/
theorem repulsive_core_counterexample :
    (1/32 : ℝ) < directEnergy (1/1000) uniform - directEnergy (1/1000) shifted :=
  direct_counterexample (1/1000) (by norm_num) (by norm_num)

theorem pairPotential_collision_barrier (lambda : ℝ) (hlambda : 0 < lambda)
    (s : ℝ) (hs : |s| ≤ 1) (B : ℝ) (hB : 0 ≤ B) :
    ∃ delta > 0, ∀ r : ℝ, 0 < r → r < delta → B < pairPotential lambda s r :=
  collision_barrier lambda hlambda s hs B hB

#print axioms cauchy_energy_gap_lower
#print axioms strict_energy_gap
#print axioms physicalEnergy_eq_totalEnergy
#print axioms physical_counterexample
#print axioms explicit_repulsive_core_counterexample
#print axioms collision_barrier
#print axioms directEnergy_eq_physicalEnergy
#print axioms direct_counterexample
#print axioms repulsive_core_counterexample
#print axioms pairPotential_collision_barrier

end VerifiedChain
