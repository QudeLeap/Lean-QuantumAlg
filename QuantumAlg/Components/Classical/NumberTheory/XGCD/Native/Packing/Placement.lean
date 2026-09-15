/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Packing.Semantics

/-!
# Complete public XGCD packing through the original scratch scopes

Fresh allocation supplies every scratch separation needed by the original
five instructions. The actual returned store is exactly one caller write of
the original packed input words, with no initial-output or source-alias premise.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original scratch allocator returns the exact packed caller write on the same full state. -/
theorem xgcdNativePackRawOutputs_actualRecord (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width)) :
    ∃ record : Store ctx → Store ctx × (packRawOutputs outputs result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (packRawOutputs outputs result).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 = before.write result
        (packedRawValue (before.read (GCD.cellRead outputs.gcd))
          (before.read (GCD.cellRead outputs.leftCoefficient))
          (before.read (GCD.cellRead outputs.rightCoefficient))) := by
  let Post (before after : Store ctx) : Prop :=
    after = before.write result
      (packedRawValue (before.read (GCD.cellRead outputs.gcd))
        (before.read (GCD.cellRead outputs.leftCoefficient))
        (before.read (GCD.cellRead outputs.rightCoefficient)))
  apply withCells_actualRecord_post ctx (packingShapes width)
    (fun cells _ transport _ => packingBody (outputs.transport transport) cells.head.ref
      cells.tail.head.ref cells.tail.tail.head.ref (transport.liftWrite result)) Post
  intro inner cells distinct transport separated
  cases cells with
  | cons raw rest =>
    cases rest with
    | cons left rest =>
      cases rest with
      | cons right rest =>
        cases rest
        let lifted := outputs.transport transport
        let target := transport.liftWrite result
        refine ⟨fun store => (packingBodyStore lifted raw.ref left.ref right.ref target store,
          ((), ((), ((), ((), ()))))), ?_, ?_⟩
        · intro reference history historyFinite state
          refine (xgcdNativePackingBody_execute
            lifted raw.ref left.ref right.ref target reference state).trans ?_
          congr 1
          exact Subsingleton.elim _ _
        · intro source before reads
          let final := packingBodyStore lifted raw.ref left.ref right.ref target before
          let returned := transport.restrict final
          have returnedReads : transport.ReadsAs returned final :=
            transport.workspaceTransport_restrict_readsAs final
          refine ⟨returned, ?_, returnedReads⟩
          apply Store.store_eq_write_of_read_frame source returned result
          · have value := xgcdNativePackingBody_result lifted raw.ref left.ref right.ref
              target before (separated.1 (GCD.cellRead outputs.gcd))
              (separated.2.1 (GCD.cellRead outputs.gcd))
              (separated.2.2.1 (GCD.cellRead outputs.gcd))
              (separated.1 (GCD.cellRead outputs.rightCoefficient))
              (separated.2.1 (GCD.cellRead outputs.rightCoefficient))
              (by
                have different : raw.ref.key ≠ left.ref.key := distinct.1.1.symm
                simpa only [GCD.cellRead, CInputRef.storageKeys, List.mem_singleton]
                  using different)
              (by
                have different : right.ref.key ≠ left.ref.key := distinct.2.1.1
                simpa only [GCD.cellRead, CInputRef.storageKeys, List.mem_singleton]
                  using different)
            have gcdRead : before.read (GCD.cellRead lifted.gcd) =
                source.read (GCD.cellRead outputs.gcd) := reads (GCD.cellRead outputs.gcd)
            have leftRead : before.read (GCD.cellRead lifted.leftCoefficient) =
                source.read (GCD.cellRead outputs.leftCoefficient) :=
              reads (GCD.cellRead outputs.leftCoefficient)
            have rightRead : before.read (GCD.cellRead lifted.rightCoefficient) =
                source.read (GCD.cellRead outputs.rightCoefficient) :=
              reads (GCD.cellRead outputs.rightCoefficient)
            have resultRead : final.read (GCD.cellRead target) =
                returned.read (GCD.cellRead result) := returnedReads (GCD.cellRead result)
            exact resultRead.symm.trans (value.trans (by rw [gcdRead, leftRead, rightRead]))
          · intro shape other resultFree
            have free : target.key ∉ (transport.liftInput (.storage other)).storageKeys := by
              rw [transport.liftInput_storageKeys]
              simpa only [target, transport.liftWrite_key, CInputRef.storageKeys,
                List.mem_singleton] using resultFree
            have unchanged := xgcdNativePackingBody_read_other lifted raw.ref left.ref right.ref
              target before (transport.liftInput (.storage other))
              (separated.1 (.storage other)) (separated.2.1 (.storage other))
              (separated.2.2.1 (.storage other)) free
            exact (returnedReads (.storage other)).symm.trans
              (unchanged.trans (reads (.storage other)))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
