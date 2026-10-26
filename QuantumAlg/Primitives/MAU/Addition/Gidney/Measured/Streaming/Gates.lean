/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax

/-!
# Native streaming addition with actual retained carry measurements

Each stage computes the next carry before it vents the preceding carry. That
carry also xors into the supplied arbitrary dirty bit. Both helpers are the
original addressed physical systems, reused only after the actual reset word.
The zero incoming carry is simplified at the low bit [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Initial static-controlled offset xor on every original target bit. -/
def offsetGates (layout : Layout encoding width) (constant : BitVec width) :
    List (GateSpec encoding) :=
  (List.ofFn fun index : Fin width =>
    if constant.getLsbD index.val then
      [.cnot layout.control (layout.target index) (layout.control_target_ne index)]
    else []).flatten

/-- Compute the next affine carry; a static zero control omits the low Toffoli. -/
def computeCarryGates (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) : List (GateSpec encoding) :=
  let source : Fin width := ⟨index.val, by omega⟩
  if index.val = 0 then
    if constant.getLsbD index.val then
      [.toffoli (layout.target source) layout.control (layout.nextCarry wide index)
        (layout.control_target_ne source).symm (layout.target_nextCarry_ne wide index)
        (layout.control_nextCarry_ne wide index)]
    else []
  else affineToffoliGates layout.control (layout.target source) (layout.carryHelper index.val)
    (layout.nextCarry wide index) (layout.control_target_ne source) (layout.control_clean_ne _)
    (layout.target_clean_ne source _) (layout.target_nextCarry_ne wide index)
    (layout.carryHelper_nextCarry_ne wide index) false (constant.getLsbD index.val)

/-- Extract the incoming carry into the target and its original dirty output before venting. -/
def extractCarryGates (layout : Layout encoding width) (index : Fin (width - 1)) :
    List (GateSpec encoding) :=
  if positive : 0 < index.val then
    let source : Fin width := ⟨index.val, by omega⟩
    let output : Fin (width - 2) := ⟨index.val - 1, by omega⟩
    [.cnot (layout.carryHelper index.val) (layout.target source)
      (layout.target_clean_ne source _).symm,
     .cnot (layout.carryHelper index.val) (layout.dirty output)
      (layout.dirty_clean_ne output _).symm]
  else []

/-- Complete the majority carry by xoring the same selected offset into its output. -/
def finishCarryGates (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) : List (GateSpec encoding) :=
  if constant.getLsbD index.val then
    [.cnot layout.control (layout.nextCarry wide index) (layout.control_nextCarry_ne wide index)]
  else []

/-- Compute, extract, physically vent/reset, then finish one carry in chronological order. -/
def streamingStep (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    List (Instruction encoding (width - 2)) :=
  [.native (layout.computeCarryGates wide constant index),
   .native (layout.extractCarryGates index)] ++
    (if positive : 0 < index.val then
      [.vent (layout.carryHelper index.val) ⟨index.val - 1, by omega⟩]
    else []) ++ [.native (layout.finishCarryGates wide constant index)]

/-- The actual vented prefix has one physical outcome record for every carry except the last. -/
def streamingWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) : List (Instruction encoding (width - 2)) :=
  .native (layout.offsetGates constant) ::
    (List.ofFn (layout.streamingStep wide constant)).flatten

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
