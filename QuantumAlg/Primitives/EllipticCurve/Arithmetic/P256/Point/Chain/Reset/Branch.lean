/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Branch
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Character
import all QuantumAlg.Primitives.WalshHadamard.Native

/-!
# Exact same-record mask and original-word branch coefficient

The real postmeasurement Store supplies the mask used by subsequent feedback.
Each branch has the original H coefficient and retains the full outside state
and external Reference. No normalized branch-weight conclusion is inferred
without the consumer's coherent input graph.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset

noncomputable section

open Execution EncodedBit.WindowLookup NormalizedVector
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (port : WordPort)
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2))

/-- The real ordered measurement path of one named physical outcome. -/
def outcomePath (outcome : Fin (2 ^ 256)) (state : Window.Raw) :
    (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts (QubitLayout.canonical _) sameWires (Window.resultWord port) output)).Path :=
  Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts (QubitLayout.canonical _) sameWires (Window.resultWord port) output)
    (measuredEncodedBasis (QubitLayout.canonical _) sameWires (namedOutcome port outcome state))

def nextStore (mask : CWriteRef ctx (.bits 256)) (store : Store ctx)
    (outcome : Fin (2 ^ 256)) (state : Window.Raw) : Store ctx :=
  measuredWordFinalStore (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires (Window.resultWord port) output mask store
    (outcomePath (services := services) port sameWires output outcome state)

/-- The actual next Store contains the same physical outcome, including all incoming overwrites. -/
lemma nextStore_mask (distinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits 256)) (store : Store ctx) (outcome : Fin (2 ^ 256))
    (state : Window.Raw) :
    resultConstant ((nextStore (services := services) port sameWires output mask store outcome
      state).read (.storage mask.toCStorageRef)) = outcome := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  rw [resultConstant_testBit]
  exact (measuredWordFinalStore_bit_encoded (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires (Window.resultWord port) output distinct mask store
    (namedOutcome port outcome state) index).trans
      (resultSetConstant_get (Window.resultWord port) (Window.resultWord_distinct port)
        outcome state index)

private lemma named_amplitude (outcome : Fin (2 ^ 256)) (state : Window.Raw) :
    wordHadamardAmplitude (QubitLayout.canonical Window.encoding.width) (Window.resultWord port)
      ((QubitLayout.canonical _).basisEquiv.symm
        (Window.encoding.encode (namedOutcome port outcome state)))
      ((QubitLayout.canonical _).basisEquiv.symm (Window.encoding.encode state)) =
        invSqrt2 ^ 256 * WalshHadamard.walshSign outcome (port.value state.1) := by
  rw [wordHadamardAmplitude_character]
  congr 1
  unfold wordHadamardCharacter
  calc
    _ = ∏ index : Fin 256,
        if WalshHadamard.bit outcome index && WalshHadamard.bit (port.value state.1) index
          then (-1 : ℂ) else 1 := by
      apply Finset.prod_congr rfl
      intro index _
      have rowValue := (encodedPhysicalBit_decide (QubitLayout.canonical _)
        ((Window.resultWord port).bit index) (namedOutcome port outcome state)).trans
          (resultSetConstant_get (Window.resultWord port) (Window.resultWord_distinct port)
            outcome state index)
      have columnValue := (encodedPhysicalBit_decide (QubitLayout.canonical _)
        ((Window.resultWord port).bit index) state).trans
          ((Window.pointBit_get (port.bit index) state).trans (WordPort.bit_get port index state.1))
      simp only [WalshHadamard.bit, ← rowValue, ← columnValue]
      by_cases rowOne : (((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
          (Window.encoding.encode (namedOutcome port outcome state)))
            ((Window.resultWord port).bit index).wire).val = 1 <;>
        by_cases columnOne : (((QubitLayout.canonical Window.encoding.width).basisEquiv.symm
          (Window.encoding.encode state)) ((Window.resultWord port).bit index).wire).val = 1 <;>
          simp [rowOne, columnOne]
    _ = _ := WalshHadamard.Native.sign_product 256 outcome (port.value state.1)

/-- This is the operator of the same actual reset path retained in the execution equation. -/
def branchOperator (mask : CWriteRef ctx (.bits 256)) (store : Store ctx)
    (outcome : Fin (2 ^ 256)) (state : Window.Raw)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  measuredWordKraus (QubitLayout.canonical _) sameWires (Window.resultWord port)
    (Window.resultWord_distinct port) output mask store
    (outcomePath (services := services) port sameWires output outcome state) environment Reference

/-- Every physical outcome retains its exact measured character on the complete original state. -/
lemma branchOperator_ket (distinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits 256)) (store : Store ctx)
    (outcome : Fin (2 ^ 256)) (state : Window.Raw)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    (reference : Reference.Index) :
    (branchOperator (services := services) port sameWires output mask store outcome state
      environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec =
      (invSqrt2 ^ 256 * WalshHadamard.walshSign outcome (port.value state.1)) •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires
            (namedOutcome port zeroOutcome state), reference)).vec := by
  have actual := measuredWordKraus_encoded_ket (oracles := .empty) (services := services)
    (QubitLayout.canonical _) sameWires (Window.resultWord port) (Window.resultWord_distinct port)
    output mask environment store state (namedOutcome port outcome state)
    (resultSetConstant_complement (QubitLayout.canonical _) (Window.resultWord port)
      (Window.resultWord_distinct port) outcome state) reference
  have zeroed : measuredWordResetStep (oracles := .empty) (services := services)
      (QubitLayout.canonical _) sameWires (Window.resultWord port) output mask store
      (namedOutcome port outcome state) = namedOutcome port zeroOutcome state :=
    resetState_namedOutcome port sameWires output distinct mask store outcome state
  rw [zeroed] at actual
  exact actual.trans (congrArg (fun coefficient : ℂ => coefficient •
    (NormalizedVector.ket (R := Register.prod ctx.register Reference)
      (measuredEncodedBasis (QubitLayout.canonical _) sameWires
        (namedOutcome port zeroOutcome state), reference)).vec)
      (named_amplitude port outcome state))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset
