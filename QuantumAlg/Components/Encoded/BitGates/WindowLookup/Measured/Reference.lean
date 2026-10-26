/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Reset
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual result-word correction beside arbitrary coherent references

Every label in a retained measurement fiber selects the same real stored
correction. Linearity preserves its arbitrary amplitudes and external
reference labels while the actual X program clears every measured result bit.
This statement does not assert uniform branch mass without a lookup-graph promise.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution
open scoped BigOperators

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The same actual stored-mask native correction retains each external reference label exactly. -/
lemma measuredWordCorrection_reference_ket (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (store : Store ctx) (state : Data) (environment : oracles.Interpretation)
    {Reference : Register} (reference : Reference.Index) :
    (UnitaryOperator.prodTensor
      ((measuredWordCorrection (services := services) physical sameWires target distinct output mask
        store (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
          (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
          (resultReadouts physical sameWires target output)
          (measuredEncodedBasis physical sameWires state))).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis physical sameWires state, reference)).vec =
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis physical sameWires
          (measuredWordResetStep (oracles := oracles) (services := services)
            physical sameWires target output mask store state), reference)).vec := by
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    measuredWordCorrection_applyVec, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- The actual branch correction clears any coherent retained fiber with its reference unchanged. -/
lemma measuredWordCorrection_coherent_fiber (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path)
    (environment : oracles.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (state : Index → Data)
    (samePath : ∀ index, Circuit.measurementBasisPath (gates := AlgorithmGate.model)
      (oracles := oracles) (operations := BitWord.model) (classicalOracles := services)
      (allowAllocation := false) (resultReadouts physical sameWires target output)
      (measuredEncodedBasis physical sameWires (state index)) = path)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (UnitaryOperator.prodTensor
      ((measuredWordCorrection (services := services) physical sameWires target distinct output mask
        store path).matrix environment) (1 : UnitaryOperator Reference)).applyVec
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod ctx.register Reference)
              (measuredEncodedBasis physical sameWires (state index), reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis physical sameWires
            (measuredWordResetStep (oracles := oracles) (services := services)
              physical sameWires target output mask store (state index)), reference index)).vec :=
    by
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor
      ((measuredWordCorrection (services := services) physical sameWires target distinct output mask
        store path).matrix environment) (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod ctx.register Reference)) _ = _
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul, ← samePath index]
  exact congrArg (fun vector => amplitude index • vector)
    (measuredWordCorrection_reference_ket physical sameWires target distinct output mask store
      (state index) environment (reference index))

end

end QuantumAlg.EncodedBit.WindowLookup
