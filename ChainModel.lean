import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A four-site alternating chain, including every periodic image

Lengths in `Cell` are measured in half-units: eight grid steps make a
physical period of length four. The two shell coefficients count all ordered
pairs at positive and negative displacement. The unsigned coefficient is
used for a core which repels *every* pair of species.

Energies use the directed-pair average: divide the ordered-pair sum by four,
with no additional factor one half. The conventional pair energy per
particle is half this value and has exactly the same minimizers.
-/

namespace VerifiedChain

open scoped BigOperators

abbrev Cell := Fin 4 → Fin 8

def uniform : Cell := ![0, 2, 4, 6]
def shifted : Cell := ![0, 3, 4, 5]

def charge (i : Fin 4) : ℤ := if i.val % 2 = 0 then 1 else -1

def ordered (p : Cell) : Prop :=
  ∀ i j : Fin 4, i.val < j.val → (p i).val < (p j).val

theorem uniform_admissible : ordered uniform ∧ uniform 0 = 0 := by unfold ordered; decide
theorem shifted_admissible : ordered shifted ∧ shifted 0 = 0 := by unfold ordered; decide

def residue (n : ℕ) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

/-- Image displacement in half-units, from reference label `i` to label `j`
translated by `m` whole periods. -/
def displacement (p : Cell) (i j : Fin 4) (m : ℤ) : ℤ :=
  (p j).val - (p i).val + 8 * m

noncomputable def coordinate (p : Cell) (i : Fin 4) : ℝ := (p i).val / 2

theorem displacement_coordinate (p : Cell) (i j : Fin 4) (m : ℤ) :
    (displacement p i j m : ℝ) / 2 =
      coordinate p j + 4 * (m : ℝ) - coordinate p i := by
  unfold displacement coordinate
  push_cast
  ring

theorem displacement_injective (p : Cell) (i j : Fin 4) :
    Function.Injective (displacement p i j) := by
  intro m k h
  unfold displacement at h
  omega

theorem displacement_zero_iff (p : Cell) (hp : ordered p)
    (i j : Fin 4) (m : ℤ) :
    displacement p i j m = 0 ↔ i = j ∧ m = 0 := by
  constructor
  · intro h
    have hi := (p i).isLt
    have hj := (p j).isLt
    unfold displacement at h
    have hm : m = 0 := by omega
    refine ⟨?_, hm⟩
    apply Fin.ext
    by_contra hij
    have hlt : i.val < j.val ∨ j.val < i.val := by omega
    rcases hlt with hij | hji
    · have := hp i j hij
      omega
    · have := hp j i hji
      omega
  · rintro ⟨rfl, rfl⟩
    simp [displacement]

/-- A shell hits an image of label `j` to the right of label `i`. -/
def hits (p : Cell) (i j : Fin 4) (r : Fin 8) : Prop :=
  ((p i).val + r.val) % 8 = (p j).val

instance (p : Cell) (i j : Fin 4) (r : Fin 8) : Decidable (hits p i j r) :=
  inferInstanceAs (Decidable ((_ : ℕ) = _))

theorem hits_residue (p : Cell) (i j : Fin 4) (n : ℕ) :
    hits p i j (residue n) ↔ ((p i).val + n) % 8 = (p j).val := by
  unfold hits residue
  dsimp
  omega

theorem hits_iff_unique_image (p : Cell) (i j : Fin 4) (n : ℕ) :
    hits p i j (residue n) ↔
      ∃! m : ℤ, displacement p i j m = (n : ℤ) := by
  rw [hits_residue]
  constructor
  · intro h
    refine ⟨(((p i).val + n) / 8 : ℕ), ?_, ?_⟩
    · unfold displacement
      omega
    · intro m hm
      unfold displacement at hm
      omega
  · rintro ⟨m, hm, _⟩
    have hj := (p j).isLt
    unfold displacement at hm
    omega

theorem reverse_hits_iff_unique_image (p : Cell) (i j : Fin 4) (n : ℕ) :
    hits p j i (residue n) ↔
      ∃! m : ℤ, displacement p i j m = -(n : ℤ) := by
  rw [hits_residue]
  constructor
  · intro h
    refine ⟨-((((p j).val + n) / 8 : ℕ) : ℤ), ?_, ?_⟩
    · unfold displacement
      omega
    · intro m hm
      unfold displacement at hm
      omega
  · rintro ⟨m, hm, _⟩
    have hi := (p i).isLt
    unfold displacement at hm
    omega

def signedShell (p : Cell) (r : Fin 8) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (
    (if hits p i j r then charge i * charge j else 0) +
    (if hits p j i r then charge i * charge j else 0))

def unsignedShell (p : Cell) (r : Fin 8) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (
    (if hits p i j r then 1 else 0) +
    (if hits p j i r then 1 else 0))

def uniformSigned : Fin 8 → ℤ := ![8, 0, -8, 0, 8, 0, -8, 0]
def shiftedSigned : Fin 8 → ℤ := ![8, -4, 2, -4, 4, -4, 2, -4]
def uniformUnsigned : Fin 8 → ℤ := ![8, 0, 8, 0, 8, 0, 8, 0]
def shiftedUnsigned : Fin 8 → ℤ := ![8, 4, 2, 4, 4, 4, 2, 4]

set_option maxRecDepth 30000 in
theorem uniform_signed_counts : ∀ r, signedShell uniform r = uniformSigned r := by decide
set_option maxRecDepth 30000 in
theorem shifted_signed_counts : ∀ r, signedShell shifted r = shiftedSigned r := by decide
set_option maxRecDepth 30000 in
theorem uniform_unsigned_counts : ∀ r, unsignedShell uniform r = uniformUnsigned r := by decide
set_option maxRecDepth 30000 in
theorem shifted_unsigned_counts : ∀ r, unsignedShell shifted r = shiftedUnsigned r := by decide

theorem uniform_unsigned_bounds (r : Fin 8) :
    0 ≤ unsignedShell uniform r ∧ unsignedShell uniform r ≤ 8 := by
  rw [uniform_unsigned_counts]
  exact (by decide : ∀ k, 0 ≤ uniformUnsigned k ∧ uniformUnsigned k ≤ 8) r

theorem shifted_unsigned_bounds (r : Fin 8) :
    0 ≤ unsignedShell shifted r ∧ unsignedShell shifted r ≤ 8 := by
  rw [shifted_unsigned_counts]
  exact (by decide : ∀ k, 0 ≤ shiftedUnsigned k ∧ shiftedUnsigned k ≤ 8) r

/-- Per-particle energy for signed attraction/repulsion with a radial profile
specified on positive half-grid distances. -/
noncomputable def signedEnergy (p : Cell) (w : ℕ → ℝ) : ℝ :=
  -(1 / 4 : ℝ) * ∑' n : ℕ,
    (signedShell p (residue (n + 1)) : ℝ) * w (n + 1)

/-- Per-particle energy of the all-pair `1/r²` repulsive core. The physical
distance is `(n+1)/2`, so its factor four cancels the four-particle average. -/
noncomputable def coreEnergy (p : Cell) : ℝ :=
  ∑' n : ℕ, (unsignedShell p (residue (n + 1)) : ℝ) / (n + 1 : ℝ)^2

/-! ## Equality with the particle-by-particle infinite chain

The following statements establish that the shell model is the complete
infinite periodic system, rather than a truncated or nearest-neighbor model.
The weight at separation zero is omitted; for ordered cells this removes
exactly the central self-interaction, by `displacement_zero_iff`.
-/

def compatible (p : Cell) (i j : Fin 4) (d : ℤ) : Prop :=
  (d + (p i).val - (p j).val) % 8 = 0

instance (p : Cell) (i j : Fin 4) (d : ℤ) : Decidable (compatible p i j d) :=
  inferInstanceAs (Decidable ((_ : ℤ) = _))

theorem compatible_iff_image (p : Cell) (i j : Fin 4) (d : ℤ) :
    compatible p i j d ↔ ∃ m : ℤ, displacement p i j m = d := by
  unfold compatible displacement
  constructor
  · intro h
    refine ⟨(d + (p i).val - (p j).val) / 8, ?_⟩
    omega
  · rintro ⟨m, hm⟩
    omega

theorem compatible_pos (p : Cell) (i j : Fin 4) (n : ℕ) :
    compatible p i j (n : ℤ) ↔ hits p i j (residue n) := by
  rw [hits_residue]
  unfold compatible
  have hj := (p j).isLt
  omega

theorem compatible_neg (p : Cell) (i j : Fin 4) (n : ℕ) :
    compatible p i j (-(n : ℤ)) ↔ hits p j i (residue n) := by
  rw [hits_residue]
  unfold compatible
  have hi := (p i).isLt
  omega

noncomputable def imageMask (p : Cell) (i j : Fin 4) (g : ℤ → ℝ) (d : ℤ) : ℝ :=
  if compatible p i j d then g d else 0

theorem image_reindex (p : Cell) (i j : Fin 4) (g : ℤ → ℝ) :
    (∑' m : ℤ, g (displacement p i j m)) = ∑' d : ℤ, imageMask p i j g d := by
  have hsame (m : ℤ) : imageMask p i j g (displacement p i j m) =
      g (displacement p i j m) := by
    apply if_pos
    exact (compatible_iff_image p i j _).2 ⟨m, rfl⟩
  have hs : Function.support (imageMask p i j g) ⊆ Set.range (displacement p i j) := by
    intro d hd
    by_contra hn
    have hc : ¬compatible p i j d := fun h => hn ((compatible_iff_image p i j d).1 h)
    exact hd (if_neg hc)
  simpa only [hsame] using (displacement_injective p i j).tsum_eq hs

/-- A radial weighted interaction, with its zero-distance term removed. -/
noncomputable def radialInteraction (a : ℝ) (w : ℕ → ℝ) (d : ℤ) : ℝ :=
  if d = 0 then 0 else a * w d.natAbs

noncomputable def positiveTerm (p : Cell) (i j : Fin 4) (a : ℝ) (w : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  if hits p i j (residue (n + 1)) then a * w (n + 1) else 0

private theorem positiveTerm_summable (p : Cell) (i j : Fin 4) (a : ℝ)
    (w : ℕ → ℝ) (hw : Summable (fun n : ℕ => w (n + 1))) :
    Summable (positiveTerm p i j a w) := by
  convert (hw.mul_left a).indicator {n : ℕ | hits p i j (residue (n + 1))} using 1
  funext n
  simp only [positiveTerm, Set.indicator_apply, Set.mem_setOf_eq]

private theorem mask_positive (p : Cell) (i j : Fin 4) (a : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    imageMask p i j (radialInteraction a w) ((n + 1 : ℕ) : ℤ) =
      positiveTerm p i j a w n := by
  simp only [imageMask, radialInteraction, compatible_pos, Nat.cast_eq_zero,
    Nat.add_one_ne_zero, if_false, Int.natAbs_natCast, positiveTerm]

private theorem mask_negative (p : Cell) (i j : Fin 4) (a : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    imageMask p i j (radialInteraction a w) (-((n + 1 : ℕ) : ℤ)) =
      positiveTerm p j i a w n := by
  simp only [imageMask, radialInteraction, compatible_neg, neg_eq_zero, Nat.cast_eq_zero,
    Nat.add_one_ne_zero, if_false, Int.natAbs_neg, Int.natAbs_natCast, positiveTerm]

private theorem integer_sum_of_positive_negative (g : ℤ → ℝ) (hzero : g 0 = 0)
    (hp : Summable (fun n : ℕ => g ((n + 1 : ℕ) : ℤ)))
    (hn : Summable (fun n : ℕ => g (-((n + 1 : ℕ) : ℤ)))) :
    (∑' d : ℤ, g d) = ∑' n : ℕ,
      (g ((n + 1 : ℕ) : ℤ) + g (-((n + 1 : ℕ) : ℤ))) := by
  have hp0 : Summable (fun n : ℕ => g (n : ℤ)) := (summable_nat_add_iff 1).mp hp
  have hn' : Summable (fun n : ℕ => g (-(↑n + 1))) := by simpa using hn
  rw [tsum_of_nat_of_neg_add_one hp0 hn', hp0.tsum_eq_zero_add, Nat.cast_zero, hzero, zero_add]
  simpa only [Nat.cast_add, Nat.cast_one] using (hp.tsum_add hn).symm

/-- Every ordered pair has an absolutely convergent sum over all images. -/
theorem radial_images_summable (p : Cell) (i j : Fin 4) (a : ℝ) (w : ℕ → ℝ)
    (hw : Summable (fun n : ℕ => w (n + 1))) :
    Summable (fun m : ℤ => radialInteraction a w (displacement p i j m)) := by
  let g := imageMask p i j (radialInteraction a w)
  have hp : Summable (fun n : ℕ => g ((n + 1 : ℕ) : ℤ)) := by
    simpa only [g, mask_positive] using positiveTerm_summable p i j a w hw
  have hn : Summable (fun n : ℕ => g (-((n + 1 : ℕ) : ℤ))) := by
    simpa only [g, mask_negative] using positiveTerm_summable p j i a w hw
  have hp0 : Summable (fun n : ℕ => g (n : ℤ)) := (summable_nat_add_iff 1).mp hp
  have hg : Summable g := Summable.of_nat_of_neg_add_one hp0 (by simpa using hn)
  have hsame (m : ℤ) : g (displacement p i j m) = radialInteraction a w (displacement p i j m) :=
    if_pos ((compatible_iff_image p i j _).2 ⟨m, rfl⟩)
  simpa only [Function.comp_def, hsame] using hg.comp_injective (displacement_injective p i j)

theorem radial_images_eq_shells (p : Cell) (i j : Fin 4) (a : ℝ) (w : ℕ → ℝ)
    (hw : Summable (fun n : ℕ => w (n + 1))) :
    (∑' m : ℤ, radialInteraction a w (displacement p i j m)) =
      ∑' n : ℕ, (positiveTerm p i j a w n + positiveTerm p j i a w n) := by
  rw [image_reindex]
  have hzero : imageMask p i j (radialInteraction a w) 0 = 0 := by
    simp [imageMask, radialInteraction]
  have hp : Summable (fun n : ℕ => imageMask p i j (radialInteraction a w)
      ((n + 1 : ℕ) : ℤ)) := by
    simpa only [mask_positive] using positiveTerm_summable p i j a w hw
  have hn : Summable (fun n : ℕ => imageMask p i j (radialInteraction a w)
      (-((n + 1 : ℕ) : ℤ))) := by
    simpa only [mask_negative] using positiveTerm_summable p j i a w hw
  rw [integer_sum_of_positive_negative _ hzero hp hn]
  simp only [mask_positive, mask_negative]

noncomputable def imageSum (p : Cell) (a : Fin 4 → Fin 4 → ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑' m : ℤ,
    radialInteraction (a i j) w (displacement p i j m)

noncomputable def weightedShell (p : Cell) (a : Fin 4 → Fin 4 → ℝ) (r : Fin 8) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (
    (if hits p i j r then a i j else 0) +
    (if hits p j i r then a i j else 0))

/-- The full all-images interaction is precisely its increasing-distance shell
sum. This equality holds for any summable profile, not just the examples. -/
theorem imageSum_eq_shellSum (p : Cell) (a : Fin 4 → Fin 4 → ℝ) (w : ℕ → ℝ)
    (hw : Summable (fun n : ℕ => w (n + 1))) :
    imageSum p a w = ∑' n : ℕ, weightedShell p a (residue (n + 1)) * w (n + 1) := by
  let b (i j : Fin 4) (n : ℕ) :=
    positiveTerm p i j (a i j) w n + positiveTerm p j i (a i j) w n
  have hb (i j : Fin 4) : Summable (b i j) :=
    (positiveTerm_summable p i j (a i j) w hw).add
      (positiveTerm_summable p j i (a i j) w hw)
  unfold imageSum
  simp_rw [radial_images_eq_shells p _ _ _ w hw]
  change (∑ i : Fin 4, ∑ j : Fin 4, ∑' n, b i j n) = _
  have swapJ (i : Fin 4) : (∑ j : Fin 4, ∑' n, b i j n) = ∑' n, ∑ j : Fin 4, b i j n :=
    (Summable.tsum_finsetSum (fun j _ => hb i j)).symm
  simp_rw [swapJ]
  rw [← Summable.tsum_finsetSum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    summable_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => hb i j))]
  apply tsum_congr
  intro n
  simp only [weightedShell, b, positiveTerm, Finset.sum_mul, add_mul, ite_mul, zero_mul]

theorem weightedShell_signed (p : Cell) (r : Fin 8) :
    weightedShell p (fun i j => ((charge i * charge j : ℤ) : ℝ)) r =
      (signedShell p r : ℝ) := by
  simp only [weightedShell, signedShell, Int.cast_sum, Int.cast_add, Int.cast_ite, Int.cast_zero]

theorem weightedShell_unsigned (p : Cell) (r : Fin 8) :
    weightedShell p (fun _ _ => (1 : ℝ)) r = (unsignedShell p r : ℝ) := by
  simp only [weightedShell, unsignedShell, Int.cast_sum, Int.cast_add, Int.cast_ite,
    Int.cast_zero, Int.cast_one]

theorem signedEnergy_eq_imageSum (p : Cell) (w : ℕ → ℝ)
    (hw : Summable (fun n : ℕ => w (n + 1))) :
    signedEnergy p w = -(1 / 4 : ℝ) *
      imageSum p (fun i j => ((charge i * charge j : ℤ) : ℝ)) w := by
  rw [imageSum_eq_shellSum p _ w hw]
  simp only [weightedShell_signed, signedEnergy]

theorem coreEnergy_eq_imageSum (p : Cell)
    (hw : Summable (fun n : ℕ => (4 : ℝ) / (n + 1 : ℝ)^2)) :
    coreEnergy p = (1 / 4 : ℝ) *
      imageSum p (fun _ _ => 1) (fun n => (4 : ℝ) / (n : ℝ)^2) := by
  have hw' : Summable (fun n : ℕ => (4 : ℝ) / ((n + 1 : ℕ) : ℝ)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hw
  rw [imageSum_eq_shellSum p (fun _ _ => 1) (fun n => (4 : ℝ) / (n : ℝ)^2) hw']
  simp only [weightedShell_unsigned, Nat.cast_add, Nat.cast_one]
  have heq : (fun n : ℕ => (unsignedShell p (residue (n + 1)) : ℝ) *
      ((4 : ℝ) / (n + 1 : ℝ)^2)) =
      (fun n : ℕ => 4 * ((unsignedShell p (residue (n + 1)) : ℝ) / (n + 1 : ℝ)^2)) := by
    funext n
    ring
  rw [heq, tsum_mul_left]
  unfold coreEnergy
  ring

/-- The ordinary coordinate formula, with precisely the central self pair
removed. No distances or periods are truncated. -/
noncomputable def literalPairSum (p : Cell) (a : Fin 4 → Fin 4 → ℝ)
    (F : ℝ → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ∑' m : ℤ,
    if i = j ∧ m = 0 then 0 else
      a i j * F (coordinate p j + 4 * (m : ℝ) - coordinate p i)

theorem imageSum_eq_literalPairSum (p : Cell) (hp : ordered p)
    (a : Fin 4 → Fin 4 → ℝ) (w : ℕ → ℝ) (F : ℝ → ℝ)
    (hF : ∀ d : ℤ, w d.natAbs = F ((d : ℝ) / 2)) :
    imageSum p a w = literalPairSum p a F := by
  unfold imageSum literalPairSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply tsum_congr
  intro m
  simp only [radialInteraction, displacement_zero_iff p hp, hF, displacement_coordinate]

theorem literal_images_summable (p : Cell) (hp : ordered p)
    (a : Fin 4 → Fin 4 → ℝ) (w : ℕ → ℝ) (F : ℝ → ℝ)
    (hw : Summable (fun n : ℕ => w (n + 1)))
    (hF : ∀ d : ℤ, w d.natAbs = F ((d : ℝ) / 2)) (i j : Fin 4) :
    Summable (fun m : ℤ => if i = j ∧ m = 0 then 0 else
      a i j * F (coordinate p j + 4 * (m : ℝ) - coordinate p i)) := by
  simpa only [radialInteraction, displacement_zero_iff p hp, hF, displacement_coordinate] using
    radial_images_summable p i j (a i j) w hw

#print axioms hits_iff_unique_image
#print axioms uniform_signed_counts
#print axioms shifted_unsigned_counts
#print axioms imageSum_eq_shellSum
#print axioms imageSum_eq_literalPairSum

end VerifiedChain
