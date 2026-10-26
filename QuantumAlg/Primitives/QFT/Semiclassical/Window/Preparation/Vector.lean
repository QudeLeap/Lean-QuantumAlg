/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Preparation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Feed

/-!
# Actual H preparation equals uniform source feeding on the zero-bank subspace

The selected bank's zero support is explicit. Every saved physical and
Reference amplitude is arbitrary. The identity uses the actual literal H
matrix and an injective full-layout coordinate, without a control-sized
physical allocation or a circuit permutation.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open NormalizedVector
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

private abbrev Remainder (ports : Ports ctx totalBits active) (Reference : Register) :=
  ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection × Reference.Index

/-- Arbitrary complete saved amplitudes, on the real selected zero-bank subspace. -/
def zeroBankInput (ports : Ports ctx totalBits active) (Reference : Register)
    (saved : Remainder ports Reference → Complex) : HilbertVector (ctx.register.prod Reference) :=
  WithLp.toLp 2 fun row =>
    if (referenceBankCoordinates ports.wires ports.qubits Reference row).1 =
        Partner.zeroBits active then
      saved (referenceBankCoordinates ports.wires ports.qubits Reference row).2
    else 0

/-- The actual uniform amplitude has no restriction on any remaining physical or Reference index. -/
def uniformBankVector (ports : Ports ctx totalBits active) (Reference : Register)
    (saved : Remainder ports Reference → Complex) : HilbertVector (ctx.register.prod Reference) :=
  WithLp.toLp 2 fun row =>
    invSqrt2 ^ active * saved (referenceBankCoordinates ports.wires ports.qubits Reference row).2

/-- The true sequential native H matrix gives the exact uniform amplitude on every saved vector. -/
lemma window_preparation_zero_vector (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (saved : Remainder ports Reference → Complex) :
    (preparationOperator ports environment Reference).applyVec
        (zeroBankInput ports Reference saved) = uniformBankVector ports Reference saved := by
  ext row
  let coordinates := referenceBankCoordinates ports.wires ports.qubits Reference
  let target := coordinates.symm (Partner.zeroBits active, (coordinates row).2)
  have targetCoordinates : coordinates target =
      (Partner.zeroBits active, (coordinates row).2) := coordinates.apply_symm_apply _
  change (∑ column, preparationOperator ports environment Reference row column *
      (if (coordinates column).1 = Partner.zeroBits active then saved (coordinates column).2
        else 0)) = invSqrt2 ^ active * saved (coordinates row).2
  calc
    _ = preparationOperator ports environment Reference row target *
        (if (coordinates target).1 = Partner.zeroBits active then saved (coordinates target).2
          else 0) := by
      apply Finset.sum_eq_single target
      · intro column _ different
        by_cases zero : (coordinates column).1 = Partner.zeroBits active
        · have separate : (coordinates row).2 ≠ (coordinates column).2 := by
            intro same
            apply different
            apply coordinates.injective
            have pair : coordinates column =
                (Partner.zeroBits active, (coordinates row).2) := Prod.ext zero same.symm
            exact pair.trans targetCoordinates.symm
          have actualSeparate :
              (referenceBankCoordinates ports.wires ports.qubits Reference row).2 ≠
                (referenceBankCoordinates ports.wires ports.qubits Reference column).2 := separate
          rw [window_preparation_zero_column ports environment Reference row column zero,
            if_neg actualSeparate, zero_mul]
        · rw [if_neg zero, mul_zero]
      · simp
    _ = _ := by
      rw [window_preparation_zero_column ports environment Reference row target
        (congrArg Prod.fst targetCoordinates)]
      have same : (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
          (referenceBankCoordinates ports.wires ports.qubits Reference target).2 :=
        (congrArg Prod.snd targetCoordinates).symm
      rw [if_pos same, targetCoordinates]
      simp only [if_true]

/-- Uniform mathematical source feeding equals the same real H preparation, entry for entry. -/
lemma window_preparation_uniform_source (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (saved : Remainder ports Reference → Complex) :
    (Source.feedOperator ports Reference).applyVec
        (Source.uniformSourceInput ports Reference saved) =
      (preparationOperator ports environment ((Qubits active).prod Reference)).applyVec
        (zeroBankInput ports ((Qubits active).prod Reference)
          (fun coordinate =>
            if coordinate.2.1 = binaryEquiv active (Partner.zeroBits active) then
              saved (coordinate.1, coordinate.2.2) else 0)) := by
  rw [Source.window_sourceFeed_uniform, window_preparation_zero_vector]
  ext row
  change (if row.2.1 = binaryEquiv active (Partner.zeroBits active) then
      invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits row.1).2, row.2.2)
        else 0) =
    invSqrt2 ^ active *
      (if row.2.1 = binaryEquiv active (Partner.zeroBits active) then
        saved ((bankCoordinates ports.wires ports.qubits row.1).2, row.2.2) else 0)
  rw [mul_ite, mul_zero]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
