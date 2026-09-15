/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Complete actual signed reduction through its original lexical scopes

Actual allocation supplies the zero work word and every internal separation
condition. The complete state-path record returns the original canonical
signed residue while preserving every caller read outside its destination.
Only the original already-loaded modulus value is required by the arithmetic
contract; no inverse truth, auxiliary value or raw-coefficient range is assumed.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual lexical entry closes every internal scratch premise for the original signed residue. -/
theorem withSignedReduction_actualRecord
    (raw : CInputRef ctx (.unsignedWord (signedWidth width)))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (spec : ModulusSpec width) :
    ∃ record : Store ctx → Store ctx × (withSignedReduction raw modulus output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withSignedReduction raw modulus output).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape), output.key ∉ other.storageKeys →
          (record before).1.read other = before.read other) ∧
        ((before.read modulus).toNat = spec.modulus →
          ((record before).1.read (signedRead output)).toNat =
            (reduceRawCoefficient spec (before.read raw)).val) := by
  let Post (before after : Store ctx) : Prop :=
    (∀ {shape : CShape} (other : CInputRef ctx shape), output.key ∉ other.storageKeys →
      after.read other = before.read other) ∧
    ((before.read modulus).toNat = spec.modulus →
      (after.read (signedRead output)).toNat = (reduceRawCoefficient spec (before.read raw)).val)
  refine withCells_actualRecord_initialized_restricted_post ctx (signedReductionShapes width)
    (fun cells _ transport _ => signedReductionBody (transport.liftInput raw)
      (transport.liftInput modulus) (signedWorkCell cells) (signedNegativeCell cells)
      (signedRemainderCell cells) (transport.liftWrite output)) Post ?_
  intro inner cells distinct transport separated
  let record := signedReductionBodyStep (transport.liftInput raw) (transport.liftInput modulus)
    (signedWorkCell cells) (signedNegativeCell cells) (signedRemainderCell cells)
    (transport.liftWrite output)
  refine ⟨record, signedReductionBody_execute _ _ _ _ _ _, ?_⟩
  intro before initialized
  have entered : transport.ReadsAs (transport.restrict before) before :=
    transport.workspaceTransport_restrict_readsAs before
  have returned : transport.ReadsAs (transport.restrict (record before).1) (record before).1 :=
    transport.workspaceTransport_restrict_readsAs (record before).1
  have free : ∀ {shape : CShape} (input : CInputRef ctx shape) (index : Fin 3),
      (cellAt cells index).ref.key ∉ (transport.liftInput input).storageKeys :=
    fun input index => Cells.workspaceCells_cellAt_transport_avoids
      cells transport separated input index
  have keyInjective := workspaceCells_cellAt_key_injective cells distinct
  have workNegative : (signedWorkCell cells).key ≠ (signedNegativeCell cells).key := by
    intro same
    have impossible := congrArg Fin.val (keyInjective same)
    change 2 = 1 at impossible
    omega
  have remainderNegative : (signedRemainderCell cells).key ≠ (signedNegativeCell cells).key := by
    intro same
    have impossible := congrArg Fin.val (keyInjective same)
    change 0 = 1 at impossible
    omega
  constructor
  · intro shape other outputFree
    have liftedFree : (transport.liftWrite output).key ∉
        (transport.liftInput other).storageKeys := by
      simpa only [transport.liftWrite_key, transport.liftInput_storageKeys] using outputFree
    have frame := signedReductionBody_read_other (transport.liftInput raw)
      (transport.liftInput modulus) (signedWorkCell cells) (signedNegativeCell cells)
      (signedRemainderCell cells) (transport.liftWrite output) (transport.liftInput other)
      (free other ⟨2, by decide⟩) (free other ⟨1, by decide⟩) (free other ⟨0, by decide⟩)
      liftedFree before
    exact (returned other).symm.trans (frame.trans (entered other))
  · intro modulusValue
    have initialZero : (before.read (signedRead (signedWorkCell cells))).toNat = 0 := by
      have initial := Cells.workspaceCells_cellAt_initialized cells before initialized
        ⟨2, by change 2 < 3; decide⟩
      change before.read (signedRead (signedWorkCell cells)) =
        CShape.initialValue (.unsignedWord (signedWidth width)) at initial
      rw [initial]
      rfl
    have loaded : (before.read (transport.liftInput modulus)).toNat = spec.modulus := by
      rw [entered modulus]
      exact modulusValue
    have actual := signedReductionBody_original_value (transport.liftInput raw)
      (transport.liftInput modulus) (signedWorkCell cells) (signedNegativeCell cells)
      (signedRemainderCell cells) (transport.liftWrite output) spec before initialZero
      (free raw ⟨2, by decide⟩) (free raw ⟨1, by decide⟩)
      (free modulus ⟨2, by decide⟩) (free modulus ⟨1, by decide⟩)
      (free modulus ⟨0, by decide⟩) workNegative remainderNegative loaded
    have outputRead : (record before).1.read (signedRead (transport.liftWrite output)) =
        (transport.restrict (record before).1).read (signedRead output) := by
      simpa only [signedRead, transport.liftWrite_input] using returned (signedRead output)
    change ((transport.restrict (record before).1).read (signedRead output)).toNat = _
    refine (congrArg CShape.Value.toNat outputRead.symm).trans (actual.trans ?_)
    rw [entered raw]
    exact congrArg Fin.val
      (rawCanonicalResidue_eq_reduceRawCoefficient spec ((transport.restrict before).read raw))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction.Native
