/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Semantics
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Core.Execution.Context.Union.Unitary
import all QuantumAlg.Core.Execution.Context.Union.Unitary.State
import all QuantumAlg.Core.Execution.Unitary.Local

/-!
# Complete framed coordinate conversion and exact reference-preserving action

The actual unitary instruction retains every indexed exponent and selector
beside the original arithmetic frame and result cells. Its full density
law applies to arbitrary correlated mixed inputs and stores. Canonical
coordinate inputs additionally restore the exact original preparation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MeasuredUncompute

/-- The actual coordinate instruction tensors its original program with all real indexed systems. -/
def readyProgram (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    UnitaryCircuit AlgorithmGate.model .empty (readyContext width count).quantumLayout :=
  ContextUnion.frameUnitary (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
    (runtimeProgram width modulus coefficient coordinate)

private lemma readyProgram_matrix (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    ((readyProgram width count modulus coefficient coordinate).matrix environment.quantum) =
      UnitaryOperator.reindex
        (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
          (indexedContext width (List.range (count + 1)) List.nodup_range)
          (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)).symm
        (UnitaryOperator.prodTensor ((runtimeProgram width modulus coefficient coordinate).matrix
          environment.quantum)
          (1 : UnitaryOperator
          (indexedContext width (List.range (count + 1)) List.nodup_range).register)) := by
  apply Subtype.ext
  funext row column
  change ((ContextUnion.frameUnitary (NumeratorMeasurement.context width)
      (indexedContext width (List.range (count + 1)) List.nodup_range)
      (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)
      (runtimeProgram width modulus coefficient coordinate)).matrix
        environment.quantum) row column = _
  rw [ContextUnion.contextUnion_frameUnitary_entry]
  change _ =
    (UnitaryOperator.prodTensor ((runtimeProgram width modulus coefficient coordinate).matrix
      environment.quantum)
      (1 : UnitaryOperator
        (indexedContext width (List.range (count + 1)) List.nodup_range).register))
      ((ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
        (indexedContext width (List.range (count + 1)) List.nodup_range)
        (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)) row)
      ((ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
        (indexedContext width (List.range (count + 1)) List.nodup_range)
        (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)) column)
  rw [UnitaryOperator.prodTensor_apply]
  rfl

/-- The framed native unitary is exactly the instruction already emitted by coordinateCircuit. -/
lemma coordinateCircuit_unitary {allowAllocation : Bool}
    (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate) :
    coordinateCircuit width count modulus coefficient coordinate allowAllocation =
      Circuit.unitary (allowAllocation := allowAllocation)
        (readyProgram width count modulus coefficient coordinate) := rfl

/-- The actual coordinate operator includes identity on every external reference system. -/
def coordinateOperator (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) :
    UnitaryOperator (Register.prod (readyContext width count).register Reference) :=
  UnitaryOperator.prodTensor ((readyProgram width count modulus coefficient coordinate).matrix
    environment.quantum)
    (1 : UnitaryOperator Reference)

/-- Complete quantum-reference density follows the actual unitary on every input and history. -/
lemma coordinateCircuit_density (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext width count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (allowAllocation : Bool := true) :
    ((coordinateCircuit width count modulus coefficient coordinate allowAllocation).execute
      environment
      Reference state).quantumMarginal =
        DensityOperator.applyUnitary
          (coordinateOperator
            (environment := environment) width count modulus coefficient coordinate Reference)
          state.quantumMarginal :=
  Circuit.unitary_jointDensity
    (environment := environment) (allowAllocation := allowAllocation) (readyProgram width count
    modulus coefficient coordinate) state

/-- Every original finite store survives in its own exact transformed block. -/
lemma coordinateCircuit_block (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext width count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (readyContext width count))
    (hidden : ClassicalOracleModel.empty.HiddenState) (history : History)
    (allowAllocation : Bool := true) :
    ((coordinateCircuit width count modulus coefficient coordinate allowAllocation).execute
      environment
      Reference state).block
      (stored, (hidden, (history, ()))) =
        DensityOperator.applyUnitary
          (coordinateOperator
            (environment := environment) width count modulus coefficient coordinate Reference)
          (state.block (stored, (hidden, history))) :=
  Circuit.execute_unitary_block
    (quantumEnvironment := environment)
    (allowAllocation := allowAllocation) state (readyProgram width count
    modulus coefficient coordinate)
    stored hidden history

/-- The exact actual union basis assembles the arithmetic and complete indexed registers. -/
def readyLabel (width count : Nat)
    (original : (NumeratorMeasurement.context width).register.Index)
    (indexed : (indexedContext width (List.range (count + 1)) List.nodup_range).register.Index) :
    (readyContext width count).register.Index :=
  (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
    (indexedContext width (List.range (count + 1)) List.nodup_range)
    (indexedContext_disjoint width (List.range (count + 1)) List.nodup_range)).symm
      (original, indexed)

/-- Prepared arithmetic is assembled beside arbitrary full exponent and selector values. -/
def preparedReadyLabel (modulus count : Nat) (x y : Fin (2 ^ modulus.size))
    (indexed :
      (indexedContext modulus.size (List.range (count + 1)) List.nodup_range).register.Index) :
    (readyContext modulus.size count).register.Index :=
  readyLabel modulus.size count (InPlaceTarget.preparedBasis modulus x y) indexed

/-- The real framed unitary restores preparation and retains every indexed basis value exactly. -/
lemma readyProgram_prepared (modulus count : Nat) (positive : 0 < modulus)
    (coefficient : (ZMod modulus)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (x y : Fin (2 ^ modulus.size))
    (valid : (selectedInput coordinate x y).val < modulus)
    (indexed :
      (indexedContext modulus.size (List.range (count + 1)) List.nodup_range).register.Index) :
    ((readyProgram modulus.size count (InPlaceTarget.modulusWord modulus) coefficient
      coordinate).matrix environment.quantum).applyVec
        (NormalizedVector.ket (preparedReadyLabel modulus count x y indexed)).vec =
        (NormalizedVector.ket (readyLabel modulus.size count
          (preparedRuntimeUpdate modulus coordinate x y
            (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient
              (selectedInput coordinate x y))) indexed)).vec := by
  have original := congrArg NormalizedVector.vec
    (runtimeProgram_prepared (environment := environment.quantum)
      modulus positive coefficient coordinate x y valid)
  have framed := MeasuredPointAddition.operator_prodTensor_identity_ket
    ((runtimeProgram modulus.size (InPlaceTarget.modulusWord modulus) coefficient coordinate).matrix
      environment.quantum)
    _ _ indexed original
  have transported := MeasuredPointAddition.operator_reindex_ket
    (R := Register.prod (NumeratorMeasurement.context modulus.size).register
      (indexedContext modulus.size (List.range (count + 1)) List.nodup_range).register)
    (S := (readyContext modulus.size count).register)
    (ContextUnion.unionBasisEquiv (NumeratorMeasurement.context modulus.size)
      (indexedContext modulus.size (List.range (count + 1)) List.nodup_range)
      (indexedContext_disjoint modulus.size (List.range (count + 1)) List.nodup_range)).symm
    _ _ _ framed
  exact (congrArg (fun operator : UnitaryOperator (readyContext modulus.size count).register =>
    operator.applyVec (NormalizedVector.ket (preparedReadyLabel modulus count x y indexed)).vec)
    (readyProgram_matrix
      (environment := environment)
      modulus.size count (InPlaceTarget.modulusWord modulus) coefficient
      coordinate)).trans transported

/-- Canonical conversion keeps the entire indexed frame and arbitrary external reference jointly. -/
lemma coordinateOperator_prepared (modulus count : Nat) (positive : 0 < modulus)
    (coefficient : (ZMod modulus)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (x y : Fin (2 ^ modulus.size))
    (valid : (selectedInput coordinate x y).val < modulus)
    (indexed :
      (indexedContext modulus.size (List.range (count + 1)) List.nodup_range).register.Index)
    {Reference : Register} (reference : Reference.Index) :
    (coordinateOperator
      (environment := environment)
      modulus.size count (InPlaceTarget.modulusWord modulus) coefficient
      coordinate Reference).applyVec
        (NormalizedVector.ket (preparedReadyLabel modulus count x y indexed, reference)).vec =
      (NormalizedVector.ket (readyLabel modulus.size count
        (preparedRuntimeUpdate modulus coordinate x y
          (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient
            (selectedInput coordinate x y))) indexed, reference)).vec :=
  MeasuredPointAddition.operator_prodTensor_identity_ket _ _ _ reference
    (readyProgram_prepared
      (environment := environment) modulus count positive coefficient coordinate x y valid indexed)

/-- Pair conversion composes the actual X and Y operators in execution order. -/
def pairOperator (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    UnitaryOperator (Register.prod (readyContext width count).register Reference) :=
  coordinateOperator (environment := environment) width count modulus coefficient .y Reference *
    coordinateOperator (environment := environment) width count modulus coefficient .x Reference

/-- Actual pair conversion has an exact full density action on any mixed correlated input. -/
lemma pairCircuit_density (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext width count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (allowAllocation : Bool := true) :
    ((pairCircuit width count modulus coefficient allowAllocation).execute environment Reference
      state).quantumMarginal =
      DensityOperator.applyUnitary (pairOperator
        (environment := environment) width count modulus coefficient Reference)
        state.quantumMarginal := by
  rw [pairCircuit, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    coordinateCircuit_density (allowAllocation := allowAllocation),
    coordinateCircuit_density (allowAllocation := allowAllocation), pairOperator,
    DensityOperator.applyUnitary_mul]

/-- Both actual calls preserve every original finite store and its transformed density block. -/
lemma pairCircuit_block (width count : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext width count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (readyContext width count))
    (hidden : ClassicalOracleModel.empty.HiddenState) (history : History)
    (allowAllocation : Bool := true) :
    ((pairCircuit width count modulus coefficient allowAllocation).execute environment
      Reference state).block
      (stored, (hidden, (history, ((), ())))) =
        DensityOperator.applyUnitary (pairOperator
          (environment := environment) width count modulus coefficient Reference)
          (state.block (stored, (hidden, history))) := by
  have associated := ContextUnion.historyEquiv_block
    ((coordinateCircuit width count modulus coefficient .y allowAllocation).execute environment
      Reference
      ((coordinateCircuit width count modulus coefficient .x allowAllocation).execute environment
        Reference
        state))
    (Equiv.prodCongr (Equiv.refl ClassicalOracleModel.empty.HiddenState)
      (Equiv.prodAssoc History Unit Unit)) stored (hidden, (history, ((), ())))
  have sequence := congrArg
    (fun result : State (readyContext width count) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × (Unit × Unit))) =>
      result.block (stored, (hidden, (history, ((), ())))))
    (Circuit.execute_seq
      (environment := environment)
      (coordinateCircuit width count modulus coefficient .x allowAllocation)
      (coordinateCircuit width count modulus coefficient .y allowAllocation) state)
  have second := coordinateCircuit_block
    (environment := environment) width count modulus coefficient .y
    ((coordinateCircuit width count modulus coefficient .x allowAllocation).execute environment
      Reference state)
    stored hidden (history, ()) allowAllocation
  have first := coordinateCircuit_block
    (environment := environment) width count modulus coefficient .x
    state stored hidden history allowAllocation
  refine sequence.trans (associated.trans (second.trans ?_))
  exact (congrArg
    (DensityOperator.applyUnitary (coordinateOperator
      (environment := environment) width count modulus coefficient .y Reference))
    first).trans (DensityOperator.applyUnitary_mul _ _ _).symm

/-- Canonical pair conversion retains all prepared work, indexed systems and reference. -/
lemma pairOperator_prepared (modulus count : Nat) (positive : 0 < modulus)
    (coefficient : (ZMod modulus)ˣ) (x y : Fin (2 ^ modulus.size))
    (xValid : x.val < modulus) (yValid : y.val < modulus)
    (indexed :
      (indexedContext modulus.size (List.range (count + 1)) List.nodup_range).register.Index)
    {Reference : Register} (reference : Reference.Index) :
    (pairOperator
      (environment := environment)
      modulus.size count (InPlaceTarget.modulusWord modulus) coefficient
      Reference).applyVec (NormalizedVector.ket
        (preparedReadyLabel modulus count x y indexed, reference)).vec =
      (NormalizedVector.ket (preparedReadyLabel modulus count
        (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient x)
        (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient y)
        indexed, reference)).vec := by
  have first := coordinateOperator_prepared
    (environment := environment) modulus count positive coefficient .x x y xValid
    indexed reference
  have second := coordinateOperator_prepared
    (environment := environment) modulus count positive coefficient .y
    (Nat.FixedWidth.unitProductWord (InPlaceTarget.modulusWord modulus) positive coefficient x)
    y yValid indexed reference
  change (coordinateOperator
    (environment := environment) modulus.size count (InPlaceTarget.modulusWord modulus) coefficient
    .y Reference * coordinateOperator
      (environment := environment) modulus.size count (InPlaceTarget.modulusWord modulus)
      coefficient .x Reference).applyVec _ = _
  rw [UnitaryOperator.mul_applyVec]
  exact (congrArg (coordinateOperator
    (environment := environment) modulus.size count (InPlaceTarget.modulusWord modulus)
    coefficient .y Reference).applyVec first).trans second

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
