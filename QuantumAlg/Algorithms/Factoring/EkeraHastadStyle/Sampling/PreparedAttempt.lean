/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Family
import all QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Canonical Ekerå--Håstad circuit access

The parameter decoder and source widths determine the actual compiled member,
its native basis seed, and its mathematical terminal Born observation. The
complete execution and live-bank accounting belong to the native batch code.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical

noncomputable section

/-! ## Actual shared-word member -/

/-- Canonical physical layout of one short-DLP member. -/
def layout (N : Nat) :
    QubitLayout (ShortDLP.totalQubits (registerParameters N)) :=
  ShortDLP.layout (registerParameters N)

/-- Native source preparation with power `1 mod N` and zero shared auxiliary. -/
def preparation (N : Nat) : BasisPreparation (layout N).toQuantumLayout :=
  ⟨(layout N).binaryIndexEquiv.symm
    (ShortDLP.tripleIndex (registerParameters N) 0 0
      (ShortDLP.CompiledMAU.cleanUnitLabel (arithmeticBits N) N 1))⟩

/-- Actual native-gate short-DLP circuit selected by one retained parameter.
The two selected-power folds reuse actual MAC, word-swap and inverse-MAC
unit multipliers on the same two arithmetic words
[G17, paper.tex:186-211] [VBE95, 9511018.tex:372-416]. -/
def memberCircuit {N : Nat} (parameter : CShape.Value (ParameterShape N)) :
    UnitaryCircuit (Qubits (ShortDLP.totalQubits (registerParameters N))) :=
  ShortDLP.CompiledMAU.compiledCircuit
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit parameter) (parameterTarget parameter)

/-- The member selected by a sampled parameter is exactly the circuit for its
sealed prepared residue. -/
@[simp] theorem memberCircuit_parameterValue {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    memberCircuit (parameterValue input sample) =
      ShortDLP.CompiledMAU.compiledCircuit
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
        (preparedResidue sample).unit
        (RSA.targetUnit (preparedResidue sample).unit) := by
  unfold memberCircuit
  rw [parameterUnit_parameterValue, parameterTarget_parameterValue]

@[simp] theorem memberCircuit_physical_idx {N : Nat}
    (parameter : CShape.Value (ParameterShape N)) :
    (memberCircuit parameter).physical_idx =
      List.range (ShortDLP.totalQubits (registerParameters N)) := by
  exact ShortDLP.CompiledMAU.compiledCircuit_physical_idx
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit parameter) (parameterTarget parameter)

/-- Terminal measurement of the two exponent registers. -/
def measurement (N : Nat) : TerminalZMeasure (layout N) (measurementBits N) :=
  ShortDLP.measurement (registerParameters N)

/-! ## Strict compiled-member family -/

/-- Strict event envelope for every runtime member. -/
def memberEventCost (N : Nat) : ResourcePool .quantum :=
  ShortDLP.CompiledMAU.compiledCircuitEventEnvelope
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- Strict critical-path envelope for every runtime member. -/
def memberEventDepth (N : Nat) : DepthExpr (Resource.Event .quantum) :=
  ShortDLP.CompiledMAU.compiledCircuitDepthEnvelope
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- Closed all-one strict-event depth of the canonical real member. -/
def memberEventUnitDepth (N : Nat) : Nat :=
  ShortDLP.CompiledMAU.compiledCircuitEventUnitDepth
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- The canonical member event-depth tree evaluates to its strict closed
all-one formula. -/
theorem memberEventDepth_unit (N : Nat) :
    DepthExpr.depthEval (fun _event => 1) (memberEventDepth N) =
      memberEventUnitDepth N := by
  exact ShortDLP.CompiledMAU.compiledCircuitDepthEnvelope_unit
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- The strict member unit depth is bounded by the same complete primitive
polynomial derived from its compiled circuit tree. -/
theorem memberEventUnitDepth_le_polynomial (N : Nat) :
    memberEventUnitDepth N ≤
      ShortDLP.CompiledMAU.polynomialPrimitiveBound
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N := by
  unfold memberEventUnitDepth
  exact ShortDLP.CompiledMAU.compiledCircuitEventUnitDepth_le_polynomial
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- Actual short-DLP family selected from the retained prepared parameter. -/
def circuitFamily (N : Nat) :
    UnitaryCircuitFamily (CShape.Value (ParameterShape N))
      (Qubits (ShortDLP.totalQubits (registerParameters N))) where
  member := memberCircuit
  eventEnvelope := memberEventCost N
  member_eventCost_le := by
    intro parameter
    exact ShortDLP.CompiledMAU.compiledCircuit_eventCost_le
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
      (parameterUnit parameter) (parameterTarget parameter)
  depthEnvelope := memberEventDepth N
  member_eventDepth_le := by
    intro parameter assignment
    unfold memberCircuit memberEventDepth registerParameters
    exact ShortDLP.CompiledMAU.compiledCircuit_eventDepth_le
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
      (parameterUnit parameter) (parameterTarget parameter) assignment
  commonPhysicalIdx :=
    List.range (ShortDLP.totalQubits (registerParameters N))
  member_physical_idx := memberCircuit_physical_idx

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
