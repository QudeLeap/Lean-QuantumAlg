/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Prepared.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Program
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement

/-!
# Place the unit multiplier on its complete prepared context

The source gate list addresses the supplied word before its auxiliary word.
Preparation stores the fresh auxiliary word before the supplied word in the
runtime layout. The position permutation below maps every source gate to its
actual physical system and uses no extra wires or instructions.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Execution.OwnedQubits Accumulate.Gidney

private def inputQubitLayout (width : Nat) : QubitLayout width :=
  QubitLayout.canonical width

private theorem auxiliary_input_disjoint (width : Nat) :
    List.Disjoint (auxiliaryQubitLayout width).systemIdx
      (inputQubitLayout width).systemIdx := by
  apply List.disjoint_left.mpr
  intro physical auxiliaryMember inputMember
  rw [QubitLayout.systemIdx, List.mem_ofFn] at auxiliaryMember inputMember
  obtain ⟨auxiliaryWire, auxiliaryEq⟩ := auxiliaryMember
  obtain ⟨inputWire, inputEq⟩ := inputMember
  change width + auxiliaryWire.val = physical at auxiliaryEq
  change inputWire.val = physical at inputEq
  omega

private theorem toQuantum_append_wires {leftCount rightCount : Nat}
    (left : QubitLayout leftCount) (right : QubitLayout rightCount)
    (disjoint : List.Disjoint left.systemIdx right.systemIdx) :
    (QubitLayout.append left right disjoint).toQuantum.wires =
      left.toQuantum.wires ++ right.toQuantum.wires := by
  simp only [QuantumLayout.wires, QubitLayout.toQuantum, QubitLayout.append,
    QuantumSignature.place, QuantumSignature.qubits]
  have appendWire :
      (fun index : Fin (leftCount + rightCount) =>
        (⟨Fin.append left.physical_idx right.physical_idx index, 2⟩ : QuantumWire)) =
        Fin.append
          (fun index : Fin leftCount =>
            (⟨left.physical_idx index, 2⟩ : QuantumWire))
          (fun index : Fin rightCount =>
            (⟨right.physical_idx index, 2⟩ : QuantumWire)) := by
    funext index
    refine Fin.addCases (fun leftIndex => ?_) (fun rightIndex => ?_) index
    · simp
    · simp
  rw [appendWire, List.ofFn_fin_append]

/-- Complete qubit layout in the prepared runtime's auxiliary/source order. -/
def preparedQubitLayout (width : Nat) : QubitLayout (encoding width).width :=
  QubitLayout.append (auxiliaryQubitLayout width) (inputQubitLayout width)
    (auxiliary_input_disjoint width)

/-- The same ordered wires as the actual post-preparation runtime context. -/
def preparedSourceLayout (width : Nat) : QuantumLayout (encoding width).width :=
  (preparedQubitLayout width).toQuantum

theorem preparedSourceLayout_wires (width : Nat) :
    (preparedSourceLayout width).wires = (preparedContext width).quantumLayout.wires := by
  unfold preparedContext
  rw [← RuntimeCtx.addOwnedLayout_wires_eq_append
    (context width) auxiliaryKey (auxiliaryLayout width)
    (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)]
  rw [QuantumLayout.wires_append]
  calc
    (preparedSourceLayout width).wires =
        (auxiliaryQubitLayout width).toQuantum.wires ++
          (inputQubitLayout width).toQuantum.wires := by
      unfold preparedSourceLayout preparedQubitLayout
      exact toQuantum_append_wires (auxiliaryQubitLayout width)
        (inputQubitLayout width) (auxiliary_input_disjoint width)
    _ = (auxiliaryLayout width).wires ++ (context width).quantumLayout.wires := by
      rw [← canonical_wires width]
      rfl

/-- Exact dependent basis transport from the auxiliary/source native layout to runtime. -/
def preparedPlacementBasisEquiv (width : Nat) :
    (preparedSourceLayout width).register.Index ≃ (preparedContext width).register.Index :=
  Execution.basisOfEqualWires (preparedSourceLayout width)
    (preparedContext width).quantumLayout (preparedSourceLayout_wires width)

private def wordSwapPositionValue (width index : Nat) : Nat :=
  if index < width then width + index else index - width

/-- Every source-first bit is placed at its matching physical source or
auxiliary position in the prepared auxiliary-first layout. -/
def wordSwapPosition (width : Nat) :
    Fin (encoding width).width ↪ Fin (encoding width).width where
  toFun index := ⟨wordSwapPositionValue width index.val, by
    change wordSwapPositionValue width index.val < width + width
    have within := index.isLt
    change index.val < width + width at within
    unfold wordSwapPositionValue
    split_ifs <;> omega⟩
  inj' := by
    intro left right same
    have values := congrArg Fin.val same
    change wordSwapPositionValue width left.val =
      wordSwapPositionValue width right.val at values
    have leftWithin := left.isLt
    have rightWithin := right.isLt
    change left.val < width + width at leftWithin
    change right.val < width + width at rightWithin
    apply Fin.ext
    unfold wordSwapPositionValue at values
    split_ifs at values <;> omega

theorem wordSwapPosition_dimensions (width : Nat)
    (index : Fin (encoding width).width) :
    ((QubitLayout.canonical (encoding width).width).toQuantum.wire index).dimension =
      ((preparedSourceLayout width).wire (wordSwapPosition width index)).dimension := by
  rfl

/-- The complete multiplier's literal gates at their actual prepared wires. -/
def placedMultiplier (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (preparedSourceLayout width) :=
  UnitaryCircuit.placeAt
    (QubitLayout.canonical (encoding width).width).toQuantum
    (preparedSourceLayout width) (wordSwapPosition width)
    (wordSwapPosition_dimensions width) (program width modulus coefficient)

theorem placedMultiplier_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (placedMultiplier width modulus coefficient).eventCost =
      (program width modulus coefficient).eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

theorem placedMultiplier_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (placedMultiplier width modulus coefficient).evaluatedEventDepth (fun _ => 1) =
      (program width modulus coefficient).evaluatedEventDepth (fun _ => 1) :=
  UnitaryCircuit.placeAt_evaluatedEventDepth _ _ _ _ _ _

end

end QuantumAlg.MAU.Multiplication.Gidney
