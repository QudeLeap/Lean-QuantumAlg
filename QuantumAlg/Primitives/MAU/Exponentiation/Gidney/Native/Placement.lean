/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Context
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Gates
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Oracle
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement

/-!
# Place the literal exponentiation gates on the prepared runtime context

The native gate encoding and the runtime preparation use the same logical
field order: power, auxiliary, exponent, target. The first two words are the
freshly prepared work layout; the second two are the caller-supplied layout.
This file proves equality of those complete ordered physical wires and exposes
the resulting basis correspondence. It introduces no gate or resource event.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.SuppliedQubits

private def inputQubitLayout (exponentWidth width : Nat) :
    QubitLayout (exponentWidth + width) :=
  QubitLayout.canonical (exponentWidth + width)

private lemma work_input_disjoint (exponentWidth width : Nat) :
    List.Disjoint (workQubitLayout exponentWidth width).systemIdx
      (inputQubitLayout exponentWidth width).systemIdx := by
  apply List.disjoint_left.mpr
  intro physical workMember inputMember
  rw [QubitLayout.systemIdx, List.mem_ofFn] at workMember inputMember
  obtain ⟨workWire, workEq⟩ := workMember
  obtain ⟨inputWire, inputEq⟩ := inputMember
  change exponentWidth + width + workWire.val = physical at workEq
  change inputWire.val = physical at inputEq
  omega

private lemma toQuantum_append_wires {leftCount rightCount : Nat}
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

/-- Qubit placement of the complete literal gate encoding in runtime field order. -/
def nativeQubitLayout (exponentWidth width : Nat) :
    QubitLayout (nativeEncoding exponentWidth width).width :=
  QubitLayout.append (workQubitLayout exponentWidth width)
    (inputQubitLayout exponentWidth width)
    (work_input_disjoint exponentWidth width)

/-- Quantum-layout view on which the literal encoded-bit gate list is compiled. -/
def nativeSourceLayout (exponentWidth width : Nat) :
    QuantumLayout (nativeEncoding exponentWidth width).width :=
  (nativeQubitLayout exponentWidth width).toQuantum

/-- Binary coordinates of the source layout.  Naming this transport at the
source-layout type avoids relying on semireducible unfolding at its users. -/
def nativeSourceBasisEquiv (exponentWidth width : Nat) :
    (nativeSourceLayout exponentWidth width).register.Index ≃
      (Qubits (nativeEncoding exponentWidth width).width).Index :=
  (nativeQubitLayout exponentWidth width).basisEquiv

private lemma input_wires_eq_context (exponentWidth width : Nat) :
    (inputQubitLayout exponentWidth width).toQuantum.wires =
      (context (exponentWidth + width)).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (inputQubitLayout exponentWidth width).toQuantum.wires =
    (inputQubitLayout exponentWidth width).toQuantumLayout.wires ++ []
  rw [List.append_nil]
  rfl

/-- The literal source placement and the prepared context contain the same
ordered physical qubits, including at zero widths. -/
lemma nativeSourceLayout_wires (exponentWidth width : Nat) :
    (nativeSourceLayout exponentWidth width).wires =
      (preparedContext exponentWidth width).quantumLayout.wires := by
  unfold preparedContext
  rw [← RuntimeCtx.addOwnedLayout_wires_eq_append
    (context (exponentWidth + width)) workKey (workLayout exponentWidth width)
    (gidneyExponentWork_fresh exponentWidth width)
    (gidneyExponentWork_disjoint exponentWidth width)]
  simp only [QuantumLayout.wires_append]
  calc
    (nativeSourceLayout exponentWidth width).wires =
        (workQubitLayout exponentWidth width).toQuantum.wires ++
          (inputQubitLayout exponentWidth width).toQuantum.wires := by
      unfold nativeSourceLayout nativeQubitLayout
      exact toQuantum_append_wires (workQubitLayout exponentWidth width)
        (inputQubitLayout exponentWidth width)
        (work_input_disjoint exponentWidth width)
    _ = (workLayout exponentWidth width).wires ++
          (context (exponentWidth + width)).quantumLayout.wires := by
      rw [input_wires_eq_context]
      rfl

/-- Coordinate transport from the literal source placement to the actual
prepared runtime placement.  Giving the transport its register-index type here
keeps downstream compositions independent of unfolding `QuantumLayout.Basis`. -/
def nativePlacementBasisEquiv (exponentWidth width : Nat) :
    (nativeSourceLayout exponentWidth width).register.Index ≃
      (preparedContext exponentWidth width).register.Index :=
  Execution.basisOfEqualWires (nativeSourceLayout exponentWidth width)
    (preparedContext exponentWidth width).quantumLayout
    (nativeSourceLayout_wires exponentWidth width)

/-- Binary labels of the literal source layout in the actual prepared context. -/
def preparedBasisEquiv (exponentWidth width : Nat) :
    (preparedContext exponentWidth width).register.Index ≃
      (Qubits (nativeEncoding exponentWidth width).width).Index :=
  (nativePlacementBasisEquiv exponentWidth width).symm |>.trans
      (nativeSourceBasisEquiv exponentWidth width)

private def oraclePositionValue (exponentWidth width index : Nat) : Nat :=
  if index < exponentWidth then width + width + index
  else if index < exponentWidth + (width + width) then index - exponentWidth
  else index

/-- Reorder the complete arithmetic-oracle word into prepared runtime order.
The source is exponent, power, auxiliary, target; the destination is power,
auxiliary, exponent, target. No wire is allocated or omitted. -/
def oraclePosition (exponentWidth width : Nat) :
    Fin (oracleEncoding exponentWidth width).width ↪
      Fin (nativeEncoding exponentWidth width).width where
  toFun index := ⟨oraclePositionValue exponentWidth width index.val, by
    have within := index.isLt
    change index.val < (exponentWidth + (width + width)) + width at within
    change oraclePositionValue exponentWidth width index.val <
      (width + width) + (exponentWidth + width)
    unfold oraclePositionValue
    split_ifs <;> omega⟩
  inj' := by
    intro left right equal
    apply Fin.ext
    dsimp at equal
    have values := congrArg Fin.val equal
    change oraclePositionValue exponentWidth width left.val =
      oraclePositionValue exponentWidth width right.val at values
    unfold oraclePositionValue at values
    split_ifs at values <;> omega

/-- Numerical form of the complete field reorder, used to audit all four
word segments against their actual target positions. -/
lemma oraclePosition_val (exponentWidth width : Nat)
    (index : Fin (oracleEncoding exponentWidth width).width) :
    (oraclePosition exponentWidth width index).val =
      if index.val < exponentWidth then width + width + index.val
      else if index.val < exponentWidth + (width + width) then
        index.val - exponentWidth else index.val := by
  change oraclePositionValue exponentWidth width index.val = _
  rfl

/-- The physical reorder covers every prepared system exactly once. -/
lemma oraclePosition_surjective (exponentWidth width : Nat) :
    Function.Surjective (oraclePosition exponentWidth width) := by
  apply ((Fintype.bijective_iff_injective_and_card
    (oraclePosition exponentWidth width)).2 ?_).2
  constructor
  · exact (oraclePosition exponentWidth width).injective
  · simp only [Fintype.card_fin]
    change (exponentWidth + (width + width)) + width =
      (width + width) + (exponentWidth + width)
    omega

/-- Every source and destination wire in the reorder is a qubit. -/
lemma oraclePosition_dimensions (exponentWidth width : Nat)
    (index : Fin (oracleEncoding exponentWidth width).width) :
    (((QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum).wire
      index).dimension =
      ((nativeSourceLayout exponentWidth width).wire
        (oraclePosition exponentWidth width index)).dimension := by
  rfl

/-- Place the actual arithmetic compute-copy-uncompute program on the full
prepared source carrier, preserving its native event sequence. -/
def placedArithmeticOracle (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty (nativeSourceLayout exponentWidth width) :=
  UnitaryCircuit.placeAt
    (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum
    (nativeSourceLayout exponentWidth width)
    (oraclePosition exponentWidth width)
    (oraclePosition_dimensions exponentWidth width)
    (oracleProgram exponentWidth width modulus base)

lemma placedArithmeticOracle_eventCost (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    (placedArithmeticOracle exponentWidth width modulus base).eventCost =
      (oracleProgram exponentWidth width modulus base).eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

end

end QuantumAlg.MAU.Exponentiation.Gidney
