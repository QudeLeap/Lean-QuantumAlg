/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.UnitarySource.Conditional.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries

/-!
# Conditional source access preserving an intervening phase wire

The original selector remains first, the original source follows the phase
wire, and the phase wire is untouched. Physical placement adds no query, native
operation or work qubit to the actual conditional implementation.
-/

namespace QuantumAlg.UnitarySource.Conditional
noncomputable section

/-- Select the original control and source suffix, skipping exactly the resident phase wire. -/
def spectatorPositions (width : Nat) : Fin (1 + width) ↪ Fin (1 + (1 + width)) where
  toFun index := ⟨if index.val = 0 then 0 else 1 + index.val, by
    have bound := index.isLt
    split_ifs <;> omega⟩
  inj' := by
    intro left right same
    have values := congrArg Fin.val same
    change (if left.val = 0 then 0 else 1 + left.val) =
      (if right.val = 0 then 0 else 1 + right.val) at values
    apply Fin.ext
    split_ifs at values <;> omega

/-- Actual controlled forward or expanded conditional inverse on the original physical wires. -/
def withSpectator {width : Nat} (U : UnitaryOperator (Qubits width)) (useInverse : Bool) :
    UnitaryCircuit AlgorithmGate.model (model U true true false) (layout (1 + width)) :=
  UnitaryCircuit.placeAt (layout width) (layout (1 + width)) (spectatorPositions width)
    (fun _ => rfl) (if useInverse then inverse U else controlled U)

private theorem physical_matrix {width : Nat} (U : UnitaryOperator (Qubits width))
    (useInverse : Bool) :
    (if useInverse then inverse U else controlled U).matrix =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
        (UnitaryOperator.controlledQubits (if useInverse then U⁻¹ else U)) := by
  have binary : (if useInverse then inverse U else controlled U).binaryMatrix =
      UnitaryOperator.controlledQubits (if useInverse then U⁻¹ else U) := by
    cases useInverse
    · exact controlled_matrix U
    · exact inverse_matrix U
  have transported := congrArg
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm) binary
  exact (UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (1 + width)) _).symm.trans transported

/-- Full matrix semantics preserves every phase-wire state and arbitrary source correlations. -/
theorem withSpectator_matrix {width : Nat} (U : UnitaryOperator (Qubits width))
    (useInverse : Bool) :
    (withSpectator U useInverse).matrix =
      UnitaryCircuit.operatorAt (layout width) (layout (1 + width)) (spectatorPositions width)
        (fun _ => rfl)
        (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + width)).symm
          (UnitaryOperator.controlledQubits (if useInverse then U⁻¹ else U))) := by
  rw [withSpectator, UnitaryCircuit.placeAt_matrix, physical_matrix]

/-- The intervening physical spectator does not add a query or erase an actual native event. -/
theorem withSpectator_events {width : Nat} (U : UnitaryOperator (Qubits width))
    (useInverse : Bool) :
    (withSpectator U useInverse).eventCost =
      (if useInverse then inverse U else controlled U).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    withSpectator, UnitaryCircuit.placeAt_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- The actual dependency chain remains one step for forward control and four for inverse. -/
theorem withSpectator_depth {width : Nat} (U : UnitaryOperator (Qubits width))
    (useInverse : Bool) :
    (withSpectator U useInverse).evaluatedEventDepth (fun _ => 1) =
      if useInverse then 4 else 1 := by
  change DepthExpr.depthEval (fun _ => 1) (withSpectator U useInverse).eventDepth = _
  rw [withSpectator, UnitaryCircuit.placeAt_eventDepth]
  cases useInverse
  · rfl
  · exact inverse_depth U

end
end QuantumAlg.UnitarySource.Conditional
