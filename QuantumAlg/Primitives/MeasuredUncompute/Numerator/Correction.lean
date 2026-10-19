/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Runtime
import all QuantumAlg.Primitives.MeasuredUncompute.ReusedProduct

/-!
# Actual finite-result selection of the reused product correction

The retained numerator outcomes directly select the existing X/A/Y
product, literal Z phases and that same product's adjoint. All gates act
on the original shared runtime frame. There is no packed output word,
supplied inverse oracle, or replacement arithmetic operator
[LYL+26, sec_point_add/sec_point_add.tex:85-105].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorCorrection

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MAU.Inversion.SharedEEA EncodedBit.Word ProductPlacement

/-- The actual complete correction retains all three words and every shared EEA history wire. -/
lemma correction_physical (width : Nat) (_modulus : Fin (2 ^ width + 1))
    (_mask : Fin width → Bool) :
    (QubitLayout.canonical (frameEncoding width).width).systemIdx =
      List.range (frameEncoding width).width := by
  exact QubitLayout.canonical_systemIdx _

/-- Each stored finite vector indexes the actual existing native correction gate family. -/
def member (width : Nat) (modulus : Fin (2 ^ width + 1))
    (value : CShape.Value (.fixedVector width (.finite 2))) :
    UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width) :=
  ReusedProduct.correction width modulus (QubitReadouts.mask value)

/-- Read the retained Z outcomes and execute only their selected concrete product correction. -/
def code (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (NumeratorMeasurement.context width) (NumeratorMeasurement.context width) :=
  NumeratorRuntime.selected width (member width modulus)

/-- Each real store block selects its own native member, tensored with the unchanged reference. -/
lemma code_reference (width : Nat) (modulus : Fin (2 ^ width + 1))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (NumeratorMeasurement.context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((code width modulus).execute environment Reference state).quantumMarginal =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        ((NumeratorRuntime.program width
          (member width modulus (entry.1.read (NumeratorMeasurement.input width)))).matrix
            environment.quantum)
        (1 : UnitaryOperator Reference)).quantumMarginal :=
  NumeratorRuntime.selected_reference width (member width modulus) state

/-- Every executed branch pays for its two actual product passes and selected Z corrections. -/
lemma code_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (path : (code width modulus).Path) :
    (code width modulus).resourcePool path ≤ NativeProductCorrection.nativeBudget width := by
  change ResourcePool.ofList
    (NumeratorRuntime.program width (member width modulus path.1)).eventTrace ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, NumeratorRuntime.program_cost]
  exact ReusedProduct.correction_budget width modulus (QubitReadouts.mask path.1)

end

end QuantumAlg.MeasuredUncompute.NumeratorCorrection
