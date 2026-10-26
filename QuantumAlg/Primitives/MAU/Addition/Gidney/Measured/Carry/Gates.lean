/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Gates

/-!
# Literal native carry-xor circuit for a static controlled constant

Each recursive row first reads its original dirty predecessor and finally
reads the updated predecessor; their two Toffolis cancel the unknown original
value. The independent offset CNOT of that row occurs after its lower prefix.
Static zero low bits omit a Toffoli with a constant false control. Every other
parity-controlled Toffoli uses explicit CNOT conjugations
[G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

noncomputable section

open EncodedBit GateSpec

namespace CarryLayout

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {length : Nat}

/-- The top row initially uses the original lower dirty output as its second control. -/
def descendingTop {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) : List (GateSpec encoding) :=
  let previous : Fin (length + 1) := ⟨length - 1, by omega⟩
  let current : Fin (length + 1) := Fin.last length
  affineToffoliGates layout.control (layout.source current) (layout.output previous)
    (layout.output current) (layout.control_source_ne current)
    (layout.control_output_ne previous) (layout.source_output_ne current previous)
    (layout.source_output_ne current current)
    (layout.output_ne (by
      intro equal
      have same := congrArg Fin.val equal
      change length - 1 = length at same
      omega))
    (constant.getLsbD current.val) false

/-- The final top step also xors the selected offset into its updated lower dirty control. -/
def ascendingTop {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) : List (GateSpec encoding) :=
  let previous : Fin (length + 1) := ⟨length - 1, by omega⟩
  let current : Fin (length + 1) := Fin.last length
  affineToffoliGates layout.control (layout.source current) (layout.output previous)
    (layout.output current) (layout.control_source_ne current)
    (layout.control_output_ne previous) (layout.source_output_ne current previous)
    (layout.source_output_ne current current)
    (layout.output_ne (by
      intro equal
      have same := congrArg Fin.val equal
      change length - 1 = length at same
      omega))
    (constant.getLsbD current.val) (constant.getLsbD current.val)

/-- The zero-carry-input low step has one Toffoli precisely when the static low bit is one. -/
def lowGates (layout : CarryLayout encoding length) (constant : BitVec length) :
    List (GateSpec encoding) :=
  if nonempty : 0 < length then
    let low : Fin length := ⟨0, nonempty⟩
    if constant.getLsbD 0 then
      [.cnot layout.control (layout.source low) (layout.control_source_ne low),
       .toffoli (layout.source low) layout.control (layout.output low)
         (layout.control_source_ne low).symm (layout.source_output_ne low low)
         (layout.control_output_ne low),
       .cnot layout.control (layout.source low) (layout.control_source_ne low)]
    else []
  else []

/-- The selected offset xors into the existing final dirty output of this row. -/
def topOffsetGates {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) : List (GateSpec encoding) :=
  if constant.getLsbD length then
    [.cnot layout.control (layout.output (Fin.last length))
      (layout.control_output_ne (Fin.last length))]
  else []

/-- Native recursive rows retain both paid affine Toffolis and their one offset xor. -/
def gates : {length : Nat} → CarryLayout encoding length → BitVec length →
    List (GateSpec encoding)
  | 0, _, _ => []
  | length + 1, layout, constant =>
      if positive : 0 < length then
        layout.descendingTop constant positive ++
          gates layout.lower (constant.setWidth length) ++
            layout.topOffsetGates constant ++ layout.ascendingTop constant positive
      else layout.topOffsetGates constant ++ layout.lowGates constant

/-- Compile exactly the native gates on the supplied physical qubit layout. -/
def program (layout : CarryLayout encoding length) (constant : BitVec length)
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  programList physical oracles (layout.gates constant)

/-- The compiler realizes the complete literal word; carry arithmetic is a separate obligation. -/
lemma program_realizes_fold (layout : CarryLayout encoding length) (constant : BitVec length)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (layout.program constant physical oracles) environment
      (stepList (layout.gates constant)) :=
  realizesList physical oracles _ environment

end CarryLayout

end

end QuantumAlg.MAU.Addition.Gidney.Measured
