/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Gates

/-!
# Complete static measured constant-adder instruction word

The vented prefix xors the original carries into the dirty outputs. Two paid
stored-result Z passes surround the native carry-xor on the complemented sum.
Both target complements are actual native X words. The final carry-xor restores
the dirty outputs while its retained character removes the vented phase
[G25, main.tex:271-295]. Correctness of this literal word is proved separately.
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Actual native X on every original target bit, without workspace. -/
def complementGates (layout : Layout encoding width) : List (EncodedBit.GateSpec encoding) :=
  List.ofFn fun index : Fin width => .x (layout.target index)

/-- Each phase instruction reads exactly the actual outcome paired with its dirty output bit. -/
def phaseWord (layout : Layout encoding width) : List (Instruction encoding (width - 2)) :=
  List.ofFn fun index : Fin (width - 2) => .phase (layout.dirty index) index

/-- The source's complete streaming/phase/carry-xor/phase word for one static controlled offset. -/
def adderWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) : List (Instruction encoding (width - 2)) :=
  layout.streamingWord wide constant ++ [.native layout.complementGates] ++
    layout.phaseWord ++ [.native (layout.carryLayout.gates (constant.setWidth (width - 2)))] ++
      layout.phaseWord ++ [.native layout.complementGates]

/-- The actual measured adder uses only the supplied physical ports and existing record cells. -/
def adderCircuit (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    {ctx : RuntimeCtx .quantum}
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin (width - 2) → CWriteRef ctx (.finite 2))
    (oracles : OracleModel := .empty) (operations : ClassicalOpModel := .empty)
    (services : ClassicalOracleModel := .empty) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  Instruction.wordCircuit physical sameWires output (layout.adderWord wide constant)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
