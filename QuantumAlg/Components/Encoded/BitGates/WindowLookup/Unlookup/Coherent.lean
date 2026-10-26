/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Branch
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber.Path
import all QuantumAlg.Core.Base.Gate.SupportHybrid

/-!
# Common actual unlookup coefficient on arbitrary coherent reference families

One fixed actual outcome path applies to the whole family, because it reads
only the original result values. The same original Store feeds all physical
reset and paid feedback branches. Exact linearity retains arbitrary complex
amplitudes and external reference labels with a single common coefficient.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution NormalizedVector
open scoped BigOperators

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)

/-- One real outcome acts coherently with the same coefficient on every original graph label. -/
lemma branchOperator_graph_coherent (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (outputDistinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (separate : ∀ index, (parity index).key ∉
      (CInputRef.storage mask.toCStorageRef).storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx)
    (seed : Data) (outcome : Fin (2 ^ resultWidth))
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (graph : ∀ index, frame.Graph table (state index))
    (clean : ∀ index, frame.high.CleanFrom 0 (state index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (frame.branchOperator (services := services) physical sameWires output mask parity table store
      (namedResultPath (oracles := .empty) (services := services)
        physical sameWires frame.result output seed outcome) environment Reference).applyVec
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod ctx.register Reference)
              (measuredEncodedBasis physical sameWires (state index), reference index)).vec) =
      invSqrt2 ^ resultWidth •
        ∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires
              (resultSetConstant frame.result 0 (state index)), reference index)).vec := by
  rw [HilbertOperator.applyVec_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  have actual := frame.branchOperator_graph_ket (services := services) physical sameWires output
    outputDistinct mask parity table separate environment store (state index) (graph index)
    (clean index) outcome (reference index)
  have path := namedResultPath_seed (oracles := .empty) (services := services)
    physical sameWires frame.result frame.resultDistinct output (state index) seed outcome
  change frame.outcomePath (services := services) physical sameWires output
    (resultSetConstant frame.result outcome (state index)) = _ at path
  rw [path] at actual
  rw [actual, smul_smul, smul_smul, mul_comm (amplitude index)]

/-- Clearing a concrete graph retains orthogonality jointly with every external reference label. -/
lemma clearedGraph_reference_injective (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    {Reference : Register} {Index : Type} (state : Index → Data)
    (graph : ∀ index, frame.Graph table (state index)) (reference : Index → Reference.Index)
    (injective : Function.Injective fun index =>
      (measuredEncodedBasis physical sameWires (state index), reference index)) :
    Function.Injective fun index => (measuredEncodedBasis physical sameWires
      (resultSetConstant frame.result 0 (state index)), reference index) := by
  intro first second same
  have localBasis := congrArg Prod.fst same
  have cleared : resultSetConstant frame.result 0 (state first) =
      resultSetConstant frame.result 0 (state second) := by
    apply encoding.encode_injective
    apply physical.basisEquiv.symm.injective
    exact (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires).injective localBasis
  have original := frame.resultSet_zero_injective_graph physical table (state first) (state second)
    (graph first) (graph second) cleared
  have referenceEq := congrArg Prod.snd same
  apply injective
  change (measuredEncodedBasis physical sameWires (state first), reference first) =
    (measuredEncodedBasis physical sameWires (state second), reference second)
  exact Prod.ext (congrArg (measuredEncodedBasis physical sameWires) original)
    referenceEq

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
