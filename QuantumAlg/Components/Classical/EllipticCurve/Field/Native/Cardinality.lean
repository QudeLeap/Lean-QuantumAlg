/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Mul.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Cardinality
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Cardinality
import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native.Cardinality

/-!
# Actual field-operation cardinalities

Each actual raw operation retains its full original modulus loading. In
particular subtraction pays for both original loads, while the total
coefficient path always computes raw XGCD and signed reduction.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution
open ClassicalAlgorithms.Modular Modular.Reduce.Native
open NumberTheory.XGCD.Native NumberTheory.Checked.SignedReduction.Native

variable {width : Nat} (model : ExecutionModel) [BitWord.Selected model]
  (spec : ModulusSpec width)

/-- The actual total coefficient allowance has the original linear event ceiling. -/
theorem coefficientEnvelope_card_le :
    (coefficientEnvelope model spec).card ≤ 30 * width + 70 := by
  have loaded := ConstantWord.constantLoader_length_le model (width + 1) spec.modulus
  have raw := rawEnvelope_card model (width + 1)
  have signed := signedReductionEnvelope_card_le model width
  unfold coefficientEnvelope
  simp only [Multiset.card_add, ResourcePool.ofList, Multiset.coe_card,
    List.length_cons, List.length_nil]
  omega

/-- One actual loaded reduction pays for its loader, division and remainder resize. -/
theorem loadedReductionTrace_length_le (sourceWidth : Nat) :
    (loadedReductionTrace model sourceWidth spec).length ≤ 2 * width + 4 := by
  have loaded := ConstantWord.constantLoader_length_le model (width + 1) spec.modulus
  simp only [loadedReductionTrace, reductionEvents, List.length_append,
    List.length_cons, List.length_nil]
  omega

/-- Full multiplication precedes its actual loaded reduction. -/
theorem multiplicationTrace_length_le :
    (multiplicationTrace model spec).length ≤ 2 * width + 5 := by
  have reduced := loadedReductionTrace_length_le model spec (width + width)
  change (loadedReductionTrace model (width + width) spec).length + 1 ≤ _
  omega

/-- Both original widenings and flagged addition precede the actual loaded reduction. -/
theorem additionTrace_length_le :
    (additionTrace model spec).length ≤ 2 * width + 7 := by
  have reduced := loadedReductionTrace_length_le model spec (width + 1)
  simp only [additionTrace, additionPrefixTrace, List.length_append,
    List.length_cons, List.length_nil]
  omega

/-- The original subtraction trace retains both real modulus loaders. -/
theorem subtractionTrace_length_le :
    (subtractionTrace model spec).length ≤ 4 * width + 10 := by
  have loaded := ConstantWord.constantLoader_length_le model (width + 1) spec.modulus
  have reduced := loadedReductionTrace_length_le model spec (width + 1)
  simp only [subtractionTrace, subtractionPrefixTrace, List.length_append,
    List.length_cons, List.length_nil]
  omega

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
