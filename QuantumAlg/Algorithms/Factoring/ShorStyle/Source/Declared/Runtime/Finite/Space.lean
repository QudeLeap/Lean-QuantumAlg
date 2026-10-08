/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Space

/-!
# Every retained result and live workspace in the actual finite declared tail

The exact surviving source cells grow with the symbolic number of rounds.
A complete simultaneous sampler/recovery/reset allowance remains beside them
and the caller. Both resident and auxiliary ledgers preserve actual quantum
dimensions and roles, including the final paid pack's unchanged live context.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite

open Execution

noncomputable section

/-- Exact classical capacity retained by each real complete round. -/
def roundResultSpace (N : Nat) : SpacePool .quantum :=
  Sampler.Retained.resultSpace .quantum (modulusBits N) + Storage.resultSpace N

/-- All surviving source results coexist with one full simultaneous workspace allowance. -/
def additionalSpace (N count : Nat) : SpacePool .quantum :=
  count • roundResultSpace N + completionAdditionalSpace N

/-- Every real retained round contributes its full surviving resident capacity. -/
theorem context_resident (ctx : RuntimeCtx .quantum) (N count : Nat) :
    (context ctx N count).residentSpace = ctx.residentSpace + count • roundResultSpace N := by
  induction count generalizing ctx with
  | zero => simp only [context, zero_nsmul, add_zero]
  | succ count induction =>
      rw [context, induction, Iteration.context_resident, succ_nsmul]
      unfold roundResultSpace
      ac_rfl

/-- Every actual finite path counts its caller, retained results and full resident workspace. -/
theorem body_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (body ctx N input sameWires cells result count).Path) :
    (body ctx N input sameWires cells result count).peakResidentSpace path ≤
      ctx.residentSpace + additionalSpace N count := by
  induction count generalizing ctx with
  | zero =>
      exact (Circuit.peakResidentSpace_id path).le.trans (fun axis => Nat.le_add_right _ _)
  | succ count induction =>
      rcases path with ⟨firstPath, restPath⟩
      refine (Circuit.peakResidentSpace_seq
        (Completion.code ctx N input sameWires cells result)
        (body (Iteration.context ctx N) N input ((Iteration.quantumWires ctx N).trans sameWires)
          (Completion.cells ctx N cells) (Completion.liftWrite ctx N result) count)
        ⟨firstPath, restPath⟩).le.trans ?_
      apply SpacePool.max_le
      · exact (Completion.code_resident_le ctx N input sameWires cells result firstPath).trans
          (fun axis => by simp only [additionalSpace, Pi.add_apply]; omega)
      · have later := induction (Iteration.context ctx N)
          ((Iteration.quantumWires ctx N).trans sameWires) (Completion.cells ctx N cells)
          (Completion.liftWrite ctx N result) restPath
        have frame : (Iteration.context ctx N).residentSpace + additionalSpace N count =
            ctx.residentSpace + additionalSpace N (count + 1) := by
          rw [Iteration.context_resident]
          unfold additionalSpace roundResultSpace
          rw [succ_nsmul]
          ac_rfl
        exact later.trans_eq frame

/-- The one real final pack retains every existing resident entry without extra scratch. -/
theorem code_resident_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code ctx N input sameWires count cells result).Path) :
    (code ctx N input sameWires count cells result).peakResidentSpace path ≤
      ctx.residentSpace + additionalSpace N count := by
  rcases path with ⟨roundsPath, packedPath⟩
  refine (Circuit.peakResidentSpace_seq (body ctx N input sameWires cells result count)
    (pack ctx N input count cells result) ⟨roundsPath, packedPath⟩).le.trans ?_
  apply SpacePool.max_le
  · exact body_resident_le ctx N input sameWires count cells result roundsPath
  · have packed : (pack ctx N input count cells result).peakResidentSpace packedPath =
        (context ctx N count).residentSpace :=
      Circuit.peakResidentSpace_classical (model := executionModel input)
        (BitWord.application
          (NativeFactorScan.packOp (Finite.cells ctx N count cells) (liftWrite ctx N count result)))
        packedPath
    exact (packed.trans (context_resident ctx N count)).le.trans (fun axis => by
      simp only [additionalSpace, Pi.add_apply]
      omega)

/-- Every real retained round contributes its full surviving auxiliary capacity. -/
theorem context_auxiliary (ctx : RuntimeCtx .quantum) (N count : Nat) :
    (context ctx N count).auxiliarySpace = ctx.auxiliarySpace + count • roundResultSpace N := by
  induction count generalizing ctx with
  | zero => simp only [context, zero_nsmul, add_zero]
  | succ count induction =>
      rw [context, induction, Iteration.context_auxiliary, succ_nsmul]
      unfold roundResultSpace
      ac_rfl

/-- Every actual finite path counts its caller, retained results and full auxiliary workspace. -/
theorem body_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (body ctx N input sameWires cells result count).Path) :
    (body ctx N input sameWires cells result count).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace N count := by
  induction count generalizing ctx with
  | zero =>
      exact (Circuit.peakAuxiliarySpace_id path).le.trans (fun axis => Nat.le_add_right _ _)
  | succ count induction =>
      rcases path with ⟨firstPath, restPath⟩
      refine (Circuit.peakAuxiliarySpace_seq
        (Completion.code ctx N input sameWires cells result)
        (body (Iteration.context ctx N) N input ((Iteration.quantumWires ctx N).trans sameWires)
          (Completion.cells ctx N cells) (Completion.liftWrite ctx N result) count)
        ⟨firstPath, restPath⟩).le.trans ?_
      apply SpacePool.max_le
      · exact (Completion.code_auxiliary_le ctx N input sameWires cells result firstPath).trans
          (fun axis => by simp only [additionalSpace, Pi.add_apply]; omega)
      · have later := induction (Iteration.context ctx N)
          ((Iteration.quantumWires ctx N).trans sameWires) (Completion.cells ctx N cells)
          (Completion.liftWrite ctx N result) restPath
        have frame : (Iteration.context ctx N).auxiliarySpace + additionalSpace N count =
            ctx.auxiliarySpace + additionalSpace N (count + 1) := by
          rw [Iteration.context_auxiliary]
          unfold additionalSpace roundResultSpace
          rw [succ_nsmul]
          ac_rfl
        exact later.trans_eq frame

/-- The one real final pack retains every existing auxiliary entry without extra scratch. -/
theorem code_auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code ctx N input sameWires count cells result).Path) :
    (code ctx N input sameWires count cells result).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace N count := by
  rcases path with ⟨roundsPath, packedPath⟩
  refine (Circuit.peakAuxiliarySpace_seq (body ctx N input sameWires cells result count)
    (pack ctx N input count cells result) ⟨roundsPath, packedPath⟩).le.trans ?_
  apply SpacePool.max_le
  · exact body_auxiliary_le ctx N input sameWires count cells result roundsPath
  · have packed : (pack ctx N input count cells result).peakAuxiliarySpace packedPath =
        (context ctx N count).auxiliarySpace :=
      Circuit.peakAuxiliarySpace_classical (model := executionModel input)
        (BitWord.application
          (NativeFactorScan.packOp (Finite.cells ctx N count cells) (liftWrite ctx N count result)))
        packedPath
    exact (packed.trans (context_auxiliary ctx N count)).le.trans (fun axis => by
      simp only [additionalSpace, Pi.add_apply]
      omega)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Finite
