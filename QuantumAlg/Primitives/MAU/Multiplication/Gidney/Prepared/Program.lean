/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Prepared.Placement
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Semantics
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Core.Execution.Circuit

/-!
# Prepare and execute the unit multiplier on its actual live context

The circuit allocates one zero auxiliary word, places the literal multiplier
at the same physical source and auxiliary systems, and retains both words.
Physical placement and equal-wire transport preserve the entire native event
trace and exact phase-sensitive operator.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Accumulate.Gidney Execution.OwnedQubits

/-- Independent two-word multiplication in the canonical physical basis. -/
def multiplierPhysicalOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryOperator ((QubitLayout.canonical (encoding width).width).toQuantum).register :=
  UnitaryOperator.reindex (QubitLayout.canonical (encoding width).width).basisEquiv.symm
    (wordUnitMultiplicationOperator width modulus coefficient)

/-- Independent full-carrier arithmetic target in the actual prepared layout. -/
def preparedOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : UnitaryOperator (preparedContext width).register :=
  UnitaryOperator.reindex (preparedPlacementBasisEquiv width)
    (UnitaryCircuit.operatorAt
      (QubitLayout.canonical (encoding width).width).toQuantum
      (preparedSourceLayout width) (wordSwapPosition width)
      (wordSwapPosition_dimensions width)
      (multiplierPhysicalOperator width modulus coefficient))

/-- The actual complete native multiplier on the prepared runtime carrier. -/
def preparedUnitary (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (preparedContext width).quantumLayout :=
  Execution.unitaryOfEqualWires (preparedSourceLayout width)
    (preparedContext width).quantumLayout (preparedSourceLayout_wires width)
    (placedMultiplier width modulus coefficient)

private lemma multiplierPhysicalOperator_matrix {environment : OracleModel.empty.Interpretation}
    (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).matrix environment =
      multiplierPhysicalOperator width modulus coefficient := by
  have h := gidneyUnitMultiplication_matrix (environment := environment) width modulus coefficient
  change UnitaryOperator.reindex
      (QubitLayout.canonical (encoding width).width).basisEquiv
      ((program width modulus coefficient).matrix environment) =
        wordUnitMultiplicationOperator width modulus coefficient at h
  have h' := congrArg
    (UnitaryOperator.reindex
      (QubitLayout.canonical (encoding width).width).basisEquiv.symm) h
  rw [UnitaryOperator.unitaryOperator_reindex_cancel] at h'
  exact h'

/-- The placed literal gates equal the independent full-carrier unitary,
including every noncanonical label and external superposition. -/
lemma gidneyPreparedUnitary_matrix {environment : OracleModel.empty.Interpretation}
    (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (preparedUnitary width modulus coefficient).matrix environment =
      preparedOperator width modulus coefficient := by
  rw [preparedUnitary, Execution.unitaryOfEqualWires_matrix, placedMultiplier,
    UnitaryCircuit.placeAt_matrix, multiplierPhysicalOperator_matrix]
  rfl

/-- Placement retains the complete literal native event pool. -/
lemma gidneyPreparedUnitary_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (preparedUnitary width modulus coefficient).eventCost =
      (program width modulus coefficient).eventCost := by
  rw [preparedUnitary,
    Execution.unitaryOfEqualWires_cost (preparedSourceLayout width)
      (preparedContext width).quantumLayout (preparedSourceLayout_wires width)
      (placedMultiplier width modulus coefficient) .empty .empty,
    placedMultiplier_eventCost]

/-- Placement retains the complete unit-duration dependency depth. -/
lemma gidneyPreparedUnitary_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (preparedUnitary width modulus coefficient).evaluatedEventDepth (fun _ => 1) =
      (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) := by
  exact (congrArg (DepthExpr.depthEval (fun _ => (1 : Nat)))
    (Execution.unitaryOfEqualWires_depth (preparedSourceLayout width)
      (preparedContext width).quantumLayout (preparedSourceLayout_wires width)
      (placedMultiplier width modulus coefficient) .empty .empty)).trans
        (placedMultiplier_depth width modulus coefficient)

/-- Prepare the missing zero word and run the literal native multiplier. -/
def preparedCode (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (context width) (preparedContext width) :=
  (Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
    (context width) auxiliaryKey (auxiliaryLayout width)
    (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)).seq
      (Circuit.unitary (preparedUnitary width modulus coefficient))

end

end QuantumAlg.MAU.Multiplication.Gidney
