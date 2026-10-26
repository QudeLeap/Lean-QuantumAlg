/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Parameters
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Branch.Coherent
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Components.Encoded.Circuit.Placement

/-!
# Coherent columns through actual runtime load, inserted native arithmetic and unlookup

The matrices observe the original stored-array loader, the supplied native
program on the same physical bank, and the complete paid runtime unlookup.
No new circuit or table constructor is introduced. The native arithmetic
must establish its actual basis action and preserve the original table
graph and clean selector prefix. Under these obligations every input and
external reference receives the same positive measurement coefficient.
The complete interpreter and concrete arithmetic obligations are separate.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

noncomputable section

open Execution NormalizedVector
open scoped BigOperators

private lemma unitary_applyVec_sum {R : Register} {Index : Type} [Fintype Index]
    (operator : UnitaryOperator R) (vector : Index → HilbertVector R) :
    operator.applyVec (∑ index, vector index) =
      ∑ index, operator.applyVec (vector index) :=
  HilbertOperator.applyVec_sum (operator : HilbertOperator R) vector

private lemma reference_ket {R Reference : Register} (operator : UnitaryOperator R)
    (initial final : R.Index)
    (actual : operator.applyVec (NormalizedVector.ket initial).vec =
      (NormalizedVector.ket final).vec) (reference : Reference.Index) :
    (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)).applyVec
      (NormalizedVector.ket (R := Register.prod R Reference) (initial, reference)).vec =
        (NormalizedVector.ket (R := Register.prod R Reference) (final, reference)).vec := by
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

namespace CycleParameters

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    {wordWidth lowWidth highRemaining : Nat}
    (parameters : CycleParameters encoding ctx wordWidth lowWidth highRemaining)

/-- Observe the actual native loader selected by the original Store read. -/
def observedLoader (store : Store ctx) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  unitaryOfEqualWires parameters.physical.toQuantum ctx.quantumLayout parameters.sameWires
    (splitLookupProgram parameters.lookup parameters.physical .empty
      (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
        parameters.outsideStack)
      (tableValue (store.read parameters.source)) parameters.height)

/-- Complete retained matrix order of the original load, actual body and paid unlookup branch. -/
def insertedBranchOperator
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts parameters.physical parameters.sameWires
        parameters.frame.result parameters.output)).Path)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  RuntimeUnlookup.branchOperator parameters.frame parameters.physical parameters.sameWires
      parameters.output parameters.mask parameters.parity parameters.temporary
      (splitInputs parameters.source) store path environment Reference *
    (UnitaryOperator.prodTensor (body.matrix environment) (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod ctx.register Reference)) *
    (UnitaryOperator.prodTensor ((parameters.observedLoader store).matrix environment)
      (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference))

/-- Actual dirty-target loading retains the complete physical bank and arbitrary reference. -/
lemma observedLoader_reference_ket (environment : OracleModel.empty.Interpretation)
    (store : Store ctx) (state : Data) (clean : parameters.lookup.CleanFrom 0 state)
    {Reference : Register} (reference : Reference.Index) :
    (UnitaryOperator.prodTensor ((parameters.observedLoader store).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis parameters.physical parameters.sameWires state, reference)).vec =
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis parameters.physical parameters.sameWires
          (splitLookupStep parameters.lookup
            (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
              parameters.outsideStack)
            (tableValue (store.read parameters.source)) state), reference)).vec :=
  reference_ket _ _ _ (UnitaryCircuit.equalWires_apply_encoded_ket_of_eq ctx.quantumLayout
    parameters.sameWires _ environment state _
    (splitLookupProgram_apply_encoded_ket parameters.lookup parameters.physical .empty _
      (tableValue (store.read parameters.source)) parameters.height parameters.covered
      environment state clean)) reference

/-- The same original-table graph gives a common coefficient after the actual inserted body. -/
lemma insertedBranchOperator_coherent
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (outputDistinct : Function.Injective fun index => (parameters.output index).key)
    (protection : RuntimeRow.Protection (.storage parameters.mask.toCStorageRef)
      parameters.parity parameters.temporary
      (fun row : Bool × Fin (2 ^ highRemaining) =>
        splitInputs parameters.source row.1 row.2))
    (outputFree : ∀ index top row column,
      (parameters.output index).key ∉ (splitInputs parameters.source top row column).storageKeys)
    (maskFree : ∀ top row column,
      parameters.mask.key ∉ (splitInputs parameters.source top row column).storageKeys)
    (environment : OracleModel.empty.Interpretation) (store : Store ctx)
    (seed : Data) (outcome : Fin (2 ^ wordWidth))
    {Reference : Register} {Index : Type} [Fintype Index] (initial after : Index → Data)
    (lookupClean : ∀ index, parameters.lookup.CleanFrom 0 (initial index))
    (bodyActual : ∀ index, (body.matrix environment).applyVec
      (NormalizedVector.ket (measuredEncodedBasis parameters.physical parameters.sameWires
        (splitLookupStep parameters.lookup
          (parameters.frame.cycleTarget parameters.lookup parameters.outsideAddress
            parameters.outsideStack)
          (tableValue (store.read parameters.source)) (initial index)))).vec =
      (NormalizedVector.ket
        (measuredEncodedBasis parameters.physical parameters.sameWires (after index))).vec)
    (graph : ∀ index, parameters.frame.Graph
      (fun top row => RuntimeRow.readTable (splitInputs parameters.source top row) store)
        (after index))
    (unlookupClean : ∀ index, parameters.frame.high.CleanFrom 0 (after index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (parameters.insertedBranchOperator body store
      (namedResultPath (oracles := .empty) (services := services)
        parameters.physical parameters.sameWires parameters.frame.result parameters.output
        seed outcome) environment Reference).applyVec
      (∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis parameters.physical parameters.sameWires (initial index),
            reference index)).vec) =
      invSqrt2 ^ wordWidth • ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis parameters.physical parameters.sameWires
            (resultSetConstant parameters.frame.result 0 (after index)), reference index)).vec := by
  have through :
      (UnitaryOperator.prodTensor (body.matrix environment)
        (1 : UnitaryOperator Reference)).applyVec
        ((UnitaryOperator.prodTensor ((parameters.observedLoader store).matrix environment)
          (1 : UnitaryOperator Reference)).applyVec
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod ctx.register Reference)
              (measuredEncodedBasis parameters.physical parameters.sameWires (initial index),
                reference index)).vec)) =
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis parameters.physical parameters.sameWires (after index),
            reference index)).vec := by
    rw [unitary_applyVec_sum, unitary_applyVec_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_smul,
      parameters.observedLoader_reference_ket environment store (initial index) (lookupClean index),
      reference_ket _ _ _ (bodyActual index)]
  simp only [UnitaryOperator.applyVec] at through
  rw [insertedBranchOperator, HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, through]
  exact RuntimeUnlookup.branchOperator_graph_coherent parameters.frame parameters.physical
    parameters.sameWires parameters.output outputDistinct parameters.mask parameters.parity
    parameters.temporary (splitInputs parameters.source) protection outputFree maskFree
    environment store seed outcome after graph unlookupClean reference amplitude

end CycleParameters

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
