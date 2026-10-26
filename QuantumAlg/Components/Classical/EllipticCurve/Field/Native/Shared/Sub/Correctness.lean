/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Correctness
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write

/-!
# Exact caller Store of allocated shared-modulus subtraction

The real four-cell arithmetic allocation discharges every scratch-separation
condition. The same shared modulus remains live and unchanged; after all
releases, the caller Store differs only at its actual result cell.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

open Execution ClassicalWorkspace Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma scratch_keys (cells : Cells ctx (subShapes width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) :
    subWrittenKeys (subScratch cells modulus) = cells.keys.reverse := by
  cases cells with
  | cons difference rest =>
    cases rest with
    | cons augmented rest =>
      cases rest with
      | cons right rest =>
        cases rest with
        | cons left rest => cases rest; rfl

private lemma scratch_separation {outer : RuntimeCtx kind}
    (left right : CInputRef outer (.unsignedWord width))
    (modulus : CWriteRef outer (.unsignedWord (width + 1)))
    (cells : Cells ctx (subShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    SubSeparation (transport.liftInput left) (transport.liftInput right)
      (subScratch cells (transport.liftWrite modulus)) := by
  have free {shape : CShape} (input : CInputRef outer shape) :
      ∀ key ∈ subWrittenKeys (subScratch cells (transport.liftWrite modulus)),
        key ∉ (transport.liftInput input).storageKeys := by
    intro key member
    rw [scratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) input
  constructor
  · rw [scratch_keys]
    simpa only [List.nodup_reverse] using Cells.workspaceCells_distinct_keys_nodup cells distinct
  · exact free left
  · exact free right
  · exact free (reductionRead modulus)

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual fresh allocation yields one exact caller write for arbitrary original operands. -/
lemma subIntoWord_actualRecord (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ∃ step : Store ctx → Store ctx × (subIntoWord (model := model) left right modulus output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (subIntoWord (model := model) left right modulus output).execute environment Reference
          state = state.mapClassical (fun entry => ((step entry.1).1,
            (entry.2.1, (entry.2.2, (step entry.1).2))))) ∧
      ∀ before : Store ctx, (step before).1 = before.write output
        (subValue (before.read left) (before.read right) (before.read (reductionRead modulus))) :=
    by
  apply withCells_actualStoreRecord_post (environment := environment) ctx (subShapes width)
    (fun cells _ transport _ => subBody (transport.liftInput left) (transport.liftInput right)
      (subScratch cells (transport.liftWrite modulus)) (transport.liftWrite output))
    (fun source target => target = source.write output
      (subValue (source.read left) (source.read right) (source.read (reductionRead modulus))))
  intro inner cells distinct transport separated
  have free {shape : CShape} (input : CInputRef ctx shape) :
      ∀ key ∈ subWrittenKeys (subScratch cells (transport.liftWrite modulus)),
        key ∉ (transport.liftInput input).storageKeys := by
    intro key member
    rw [scratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) input
  refine ⟨subBodyStep (transport.liftInput left) (transport.liftInput right)
    (subScratch cells (transport.liftWrite modulus)) (transport.liftWrite output),
    subBody_execute _ _ _ _, ?_⟩
  intro source before reads
  let value := subValue (source.read left) (source.read right) (source.read (reductionRead modulus))
  refine ⟨source.write output value, rfl, ?_⟩
  have result := subBody_store (transport.liftInput left) (transport.liftInput right)
    (subScratch cells (transport.liftWrite modulus))
    (scratch_separation left right modulus cells distinct transport separated)
    (transport.liftWrite output) before
  have valueSame : subValue (before.read (transport.liftInput left))
      (before.read (transport.liftInput right))
      (before.read (reductionRead (transport.liftWrite modulus))) = value := by
    change subValue (before.read (transport.liftInput left))
      (before.read (transport.liftInput right))
      (before.read (transport.liftInput (reductionRead modulus))) = _
    rw [reads left, reads right, reads (reductionRead modulus)]
  have scratchReads : transport.ReadsAs source (subStore (transport.liftInput left)
      (transport.liftInput right) (subScratch cells (transport.liftWrite modulus)) before) := by
    intro shape input
    exact (subStore_preserves _ _ _ _ (transport.liftInput input) (free input)).trans (reads input)
  change (subBodyStep (transport.liftInput left) (transport.liftInput right)
      (subScratch cells (transport.liftWrite modulus)) (transport.liftWrite output) before).1 =
    (subStore (transport.liftInput left) (transport.liftInput right)
      (subScratch cells (transport.liftWrite modulus)) before).write (transport.liftWrite output)
      (subValue (before.read (transport.liftInput left))
        (before.read (transport.liftInput right))
        (before.read (reductionRead (transport.liftWrite modulus)))) at result
  rw [valueSame] at result
  apply (congrArg (transport.ReadsAs (source.write output value)) result).mpr
  intro shape input
  exact transport.workspaceTransport_readsAs_write scratchReads output value input

/-- Certified chronological record of the already-defined shared-modulus program. -/
def subIntoWordStep (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (subIntoWord (model := model) left right modulus output).Path :=
  Classical.choose (subIntoWord_actualRecord (environment := environment) left right modulus output)

/-- Full actual execution retains arbitrary reference blocks and prior histories. -/
lemma sharedSubIntoWord_execute (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (subIntoWord (model := model) left right modulus output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := subIntoWordStep (environment := environment) left right modulus output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  (Classical.choose_spec (subIntoWord_actualRecord (environment := environment)
    left right modulus output)).1 Reference state

/-- Exactly one caller result cell changes after all real lexical releases. -/
lemma sharedSubIntoWordStep_store (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (subIntoWordStep (environment := environment) left right modulus output store).1 =
      store.write output
        (subValue (store.read left) (store.read right) (store.read (reductionRead modulus))) :=
  (Classical.choose_spec (subIntoWord_actualRecord (environment := environment)
    left right modulus output)).2 store

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared
