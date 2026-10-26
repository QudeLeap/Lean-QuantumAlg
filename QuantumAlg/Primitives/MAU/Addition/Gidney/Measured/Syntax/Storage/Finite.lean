/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Storage

/-!
# Actual physical finite outcomes in the same declared record cells

The dimension equality casts only the finite value shape of the same physical
qubit. It changes neither a live cell key nor the actual Store write. These
equations connect physical retained outcomes to the distinct record bank
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum}

/-- Casting the same qubit's finite output shape preserves its actual live storage key. -/
lemma finiteOutput_key {dimension : ℕ+} (qubit : dimension = 2)
    (output : CWriteRef ctx (.finite 2)) :
    (finiteOutput qubit output).key = output.key := by
  cases qubit
  rfl

/-- The same actual write records the physical outcome cast to its declared qubit value. -/
lemma finiteOutput_write {dimension : ℕ+} (qubit : dimension = 2)
    (output : CWriteRef ctx (.finite 2)) (store : Store ctx) (outcome : Fin dimension) :
    store.write (finiteOutput qubit output) (.finite outcome) =
      store.write output (.finite (Fin.cast (congrArg PNat.val qubit) outcome)) := by
  cases qubit
  rfl

/-- The actual vent overwrites exactly its supplied record cell with the actual physical outcome. -/
lemma actualRecord_vent_store {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
    {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (target : EncodedBit encoding) (record : Fin records) (store : Store ctx)
    (outcome : (Instruction.vent target record).PhysicalOutcome physical sameWires) :
    ((Instruction.vent target record).actualRecord (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output store outcome).1 =
      store.write (output record) (.finite
        (EncodedBit.MeasuredUncompute.placedOutcome target physical ctx sameWires outcome)) :=
  finiteOutput_write
    (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)
    (output record) store outcome

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
