/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Read

/-!
# Actual store writes through structural workspace transport

The typed storage map preserves physical identities, while its recursive input
map retains every constructor and index. Consequently writing the same value
to a caller output and its lifted output preserves every actual caller read.
-/

namespace QuantumAlg.Execution.ClassicalWorkspace.Transport

/-- Corresponding writes preserve agreement of all actual transported caller reads. -/
lemma workspaceTransport_readsAs_write {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} (transport : Transport outer inner)
    {source : Store outer} {before : Store inner}
    (reads : transport.ReadsAs source before)
    {shape : CShape} (output : CWriteRef outer shape) (value : shape.Value) :
    transport.ReadsAs (source.write output value)
      (before.write (transport.liftWrite output) value) := by
  intro observed input
  induction input with
  | storage ref =>
      classical
      by_cases same : output.key = ref.key
      · have shapes := CStorageRef.storageRef_shape_eq_of_key output.toCStorageRef ref same
        cases shapes
        have refs := CStorageRef.storageRef_eq_of_key output.toCStorageRef ref same
        cases refs
        rw [transport.liftWrite_input, Store.read_write_same, Store.read_write_same]
      · have different : (transport.liftWrite output).key ≠ (transport.liftStorage ref).key := by
          simpa only [transport.liftWrite_key, transport.liftStorage_key] using same
        change (before.write (transport.liftWrite output) value).read
          (.storage (transport.liftStorage ref)) = (source.write output value).read (.storage ref)
        rw [Store.read_write_other _ _ _ _ different, Store.read_write_other _ _ _ _ same]
        exact reads (.storage ref)
  | product left right leftIH rightIH => exact congrArg₂ CShape.Value.product leftIH rightIH
  | fixedVector entries entriesIH => exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first input ih => exact congrArg CShape.Value.first ih
  | second input ih => exact congrArg CShape.Value.second ih
  | vectorGet input index ih => exact congrArg (fun entry => entry.get index) ih
  | bitsGet input index ih => exact congrArg (fun entry => entry.bitGet index) ih
  | wordBitGet input index ih => exact congrArg (fun entry => entry.wordBitGet index) ih

end QuantumAlg.Execution.ClassicalWorkspace.Transport
