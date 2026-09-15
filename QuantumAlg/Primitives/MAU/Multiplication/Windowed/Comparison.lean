/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.DirtyBorrowed
import all QuantumAlg.Primitives.MAU.Multiplication.Windowed.Even

/-!
# Exact comparison of windowed and HRS modular multiplication

The literal HRS multiplier performs one quadratic selected modular addition
for every bit in each of its forward and inverse passes. This module derives
a cubic lower bound from that actual circuit and proves that the exact
two-bit-window circuit has a strictly smaller native Toffoli coordinate at
every common even width of at least six bits.

This comparison is deliberately a Toffoli result, as required by R.3. It does
not claim a space improvement: the windowed program retains the established
`5*n+4` VBE layout, while the literal HRS program remains the narrower
`2*n+1` construction. Endpoint re-instantiation is a separate downstream
decision.
-/

section

namespace QuantumAlg
namespace MAU.Multiplication.Windowed.Comparison

noncomputable section

open MAU.Multiplication.DirtyBorrowed

/-- Every literal HRS selected modular-add stage contains its unconditional
quadratic controlled-adder block. -/
theorem hrsStageToffoliCount_lower (interior modulus addend : Nat) :
    4 * (interior + 2) ^ 2 ≤
      literalControlledModularAddToffoliCount interior modulus addend := by
  unfold literalControlledModularAddToffoliCount
  rw [pow_two]
  calc
    4 * ((interior + 2) * (interior + 2)) =
        4 * (interior + 2) * (interior + 2) := by ac_rfl
    _ ≤ _ :=
      (Nat.le_add_left
        (4 * (interior + 2) * (interior + 2))
        (selectedCarryToffoliClosedForm interior
          (overflowComparisonConstant (interior + 2).succ
            (modulus - addend)))).trans
        (Nat.le_add_right _ _)

private theorem length_mul_le_sum {α : Type} (bound : Nat) (cost : α → Nat)
    (hcost : ∀ item, bound ≤ cost item) :
    ∀ items : List α, items.length * bound ≤ (items.map cost).sum
  | [] => by simp
  | item :: rest => by
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      calc
        rest.length.succ * bound =
            bound + rest.length * bound := by
          rw [Nat.succ_mul rest.length bound]
          exact Nat.add_comm _ _
        _ ≤ cost item + (rest.map cost).sum :=
          Nat.add_le_add (hcost item)
            (length_mul_le_sum bound cost hcost rest)

/-- Each literal HRS accumulation pass has at least one quadratic block per
source bit. -/
theorem literalSelectedToffoliCount_lower (interior : Nat)
    (params : Parameters (interior + 2).succ) (subtract : Bool)
    (bits : List (Fin (interior + 2).succ)) :
    bits.length * (4 * (interior + 2) ^ 2) ≤
      selectedToffoliCount
        (fun bit => literalControlledModularAdd interior params bit subtract)
        bits := by
  unfold selectedToffoliCount
  apply length_mul_le_sum
  intro bit
  change 4 * (interior + 2) ^ 2 ≤
    literalControlledModularAddToffoliCount interior params.modulus
      (params.signedStageConstant subtract bit)
  exact hrsStageToffoliCount_lower _ _ _

theorem literalForwardToffoliCount_lower (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    (interior + 2).succ * (4 * (interior + 2) ^ 2) ≤
      literalForwardToffoliCount interior params := by
  unfold literalForwardToffoliCount
  change (interior + 2).succ * (4 * (interior + 2) ^ 2) ≤
    selectedToffoliCount
      (fun bit => literalControlledModularAdd interior params bit false)
      (List.ofFn fun bit : Fin (interior + 2).succ => bit)
  simpa only [List.length_ofFn] using
    literalSelectedToffoliCount_lower interior params false
      (List.ofFn fun bit : Fin (interior + 2).succ => bit)

theorem literalInverseToffoliCount_lower (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    (interior + 2).succ * (4 * (interior + 2) ^ 2) ≤
      literalInverseToffoliCount interior params := by
  unfold literalInverseToffoliCount
  change (interior + 2).succ * (4 * (interior + 2) ^ 2) ≤
    selectedToffoliCount
      (fun bit => literalControlledModularAdd interior params bit true)
      (List.ofFn fun bit : Fin (interior + 2).succ => bit).reverse
  simpa only [List.length_reverse, List.length_ofFn] using
    literalSelectedToffoliCount_lower interior params true
      (List.ofFn fun bit : Fin (interior + 2).succ => bit).reverse

/-- Cubic lower bound projected from the exact literal HRS multiplier count. -/
theorem literalInPlaceProgram_toffoli_count_lower (interior : Nat)
    (params : Parameters (interior + 2).succ) :
    8 * (interior + 2).succ * (interior + 2) ^ 2 ≤
      ResourcePool.count (.gate (.builtin "toffoli"))
        (literalInPlaceProgram interior params).eventCost := by
  rw [literalInPlaceProgram_toffoli_count_eq]
  have hforward := literalForwardToffoliCount_lower interior params
  have hinverse := literalInverseToffoliCount_lower interior params
  unfold toffoliCount
  nlinarith

/-- Interior parameter that gives the HRS circuit the same even word width as
`Even.width half`. -/
def hrsInterior (half : Nat) : Nat := 2 * half - 3

theorem hrsWordWidth_eq (half : Nat) (hhalf : 3 ≤ half) :
    (hrsInterior half + 2).succ = Even.width half := by
  unfold hrsInterior Even.width
  omega

/-- At every common even word width of at least six bits, the exact native
Toffoli count of the windowed circuit is strictly below the exact R.2 literal
HRS circuit count. Both sides are event costs of their correctness-proved
physical programs. -/
theorem windowed_toffoli_count_lt_hrs (half N : Nat) (u : (ZMod N)ˣ)
    (hhalf : 3 ≤ half)
    (params : Parameters (hrsInterior half + 2).succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (Even.multiplicationProgram half N u).eventCost <
      ResourcePool.count (.gate (.builtin "toffoli"))
        (literalInPlaceProgram (hrsInterior half) params).eventCost := by
  have hwindow := Even.multiplicationProgram_toffoli_count_le half N u
  have hhrs := literalInPlaceProgram_toffoli_count_lower
    (hrsInterior half) params
  have hwidth := hrsWordWidth_eq half hhalf
  calc
    ResourcePool.count (.gate (.builtin "toffoli"))
        (Even.multiplicationProgram half N u).eventCost ≤
        128 * half ^ 2 + 4 * half := hwindow
    _ < 8 * (hrsInterior half + 2).succ *
          (hrsInterior half + 2) ^ 2 := by
      have hinterior : hrsInterior half + 2 + 1 = 2 * half := by
        simpa only [Nat.succ_eq_add_one, Even.width] using hwidth
      nlinarith
    _ ≤ ResourcePool.count (.gate (.builtin "toffoli"))
          (literalInPlaceProgram (hrsInterior half) params).eventCost := hhrs

end

end MAU.Multiplication.Windowed.Comparison
end QuantumAlg

end
