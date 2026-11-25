import Mathlib.Tactic

/-!
An exact algebraic tail certificate for a rational interaction potential.
No floating point arithmetic or external oracle is used in these proofs.
-/

noncomputable section

namespace VerifiedChain

/-- Eight consecutive half-grid distances, with the signed pair-count difference
for the two explicit period-four cells already evaluated. -/
def cauchyBlock (x : ℝ) : ℝ :=
    -(16 / (16 + (8*x+1)^2))
    + 40 / (16 + (8*x+2)^2)
    - 16 / (16 + (8*x+3)^2)
    - 16 / (16 + (8*x+4)^2)
    - 16 / (16 + (8*x+5)^2)
    + 40 / (16 + (8*x+6)^2)
    - 16 / (16 + (8*x+7)^2)

/-- All coefficients are positive. The argument will be x-1 ≥ 0. -/
def tailPolynomial (y : ℝ) : ℝ :=
    8589934592*y^14 + 180388626432*y^13 + 1770063396864*y^12
    + 10755671851008*y^11 + 45036234342400*y^10
    + 136616991522816*y^9 + 307430271352832*y^8
    + 517518751432704*y^7 + 649893142782464*y^6
    + 600784141988352*y^5 + 398348693063104*y^4
    + 181181572322688*y^3 + 52359233436594*y^2
    + 8331458859750*y + 522821915525

def tailDenominator (x : ℝ) : ℝ :=
    800*x^2*(2*x^2+2*x+1)*(16*x^2+8*x+5)*(16*x^2+24*x+13)
      *(64*x^2+16*x+17)*(64*x^2+48*x+25)
      *(64*x^2+80*x+41)*(64*x^2+112*x+65)

theorem first_block_exact : cauchyBlock 0 = 23403 / 453050 := by
  norm_num [cauchyBlock]

theorem first_block_lower : (103 / 2000 : ℝ) < cauchyBlock 0 := by
  rw [first_block_exact]
  norm_num

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem tail_polynomial_identity (x : ℝ) (hx : 1 ≤ x) :
    cauchyBlock x + 1 / (800*x^2) =
      tailPolynomial (x-1) / tailDenominator x := by
  have hxpos : 0 < x := by linarith
  have h1 : 0 < 16 + (8*x+1)^2 := by positivity
  have h2 : 0 < 16 + (8*x+2)^2 := by positivity
  have h3 : 0 < 16 + (8*x+3)^2 := by positivity
  have h4 : 0 < 16 + (8*x+4)^2 := by positivity
  have h5 : 0 < 16 + (8*x+5)^2 := by positivity
  have h6 : 0 < 16 + (8*x+6)^2 := by positivity
  have h7 : 0 < 16 + (8*x+7)^2 := by positivity
  have hD : 0 < tailDenominator x := by
    dsimp [tailDenominator]
    positivity
  dsimp [cauchyBlock]
  field_simp
  dsimp [tailPolynomial, tailDenominator]
  ring

theorem cauchy_block_tail_bound (x : ℝ) (hx : 1 ≤ x) :
    -(1 / (800*x^2)) ≤ cauchyBlock x := by
  have hy : 0 ≤ x-1 := by linarith
  have hxpos : 0 < x := by linarith
  have hp : 0 ≤ tailPolynomial (x-1) := by
    dsimp [tailPolynomial]
    positivity
  have hd : 0 < tailDenominator x := by
    dsimp [tailDenominator]
    positivity
  have h := div_nonneg hp hd.le
  rw [← tail_polynomial_identity x hx] at h
  linarith

#print axioms first_block_lower
#print axioms cauchy_block_tail_bound

end VerifiedChain
