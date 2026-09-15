/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout.Scope

/-!
# Complete actual order-recovery execution

The body record follows its real initialization store, every stored-activity
iteration and the actual final option encoder. The enclosing execution theorem
composes that proved body with its genuine field allocations and releases,
preserving complete density blocks and their correlated finite paths.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

private theorem mapDecision {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (first second : DecidableEq D) (state : ExecutionState C R) (update : C → D) :
    @ExecutionState.mapClassical C D _ _ R first state update =
      @ExecutionState.mapClassical C D _ _ R second state update :=
  congrArg (fun decision : DecidableEq D =>
    @ExecutionState.mapClassical C D _ _ R decision state update)
      (Subsingleton.elim first second)

private def scanRecord {work : RuntimeCtx kind} {width count : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width)
    (base : CInputRef work (.canonicalResidue width))
    (cells : ScanCells work width count) (fuel : Nat) (store : Store work) :
    Store work × (scan spec base cells fuel).Path :=
  ((fun initial => (scanSlotStep spec base cells initial).1)^[fuel] store,
    fun index : Fin fuel => (scanSlotStep spec base cells
      ((fun initial => (scanSlotStep spec base cells initial).1)^[index.val] store)).2)

private theorem scanRecord_execute {work : RuntimeCtx kind} {width count : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width)
    (base : CInputRef work (.canonicalResidue width))
    (cells : ScanCells work width count) (fuel : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State work Reference History) :
    (scan spec base cells fuel).execute Reference state =
      state.mapClassical (fun entry =>
        ((scanRecord spec base cells fuel entry.1).1,
          (entry.2, (scanRecord spec base cells fuel entry.1).2))) := by
  refine (nativeScan_execute spec base cells fuel Reference state).trans ?_
  exact mapDecision _ _ state (fun entry =>
    ((scanRecord spec base cells fuel entry.1).1,
      (entry.2, (scanRecord spec base cells fuel entry.1).2)))

/-- Concrete initialization, actual finite scan paths and the final real option write. -/
def recoveryBodyStep
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    Store (recoveryContext ctx modulusWidth (phaseBits + 1)) ×
      (recoveryBody spec base sample output).Path :=
  let initialized := initializeScanStep ctx modulusWidth phaseBits sample store
  let next := scanSlotStep spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1))
  let fuel := ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits
  let scanned := (fun value => (next value).1)^[fuel] initialized.1
  let paths := fun index : Fin fuel =>
    (next ((fun value => (next value).1)^[index.val] initialized.1)).2
  (scanned.applyOp (packRecoveredOp output), (initialized.2, (paths, ())))

/-- Every actual body path is tied to the same initialization and final-store record. -/
theorem nativeRecovery_body_execute
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (recoveryContext ctx modulusWidth (phaseBits + 1)) Reference History) :
    (recoveryBody spec base sample output).execute Reference state =
      state.mapClassical (fun entry =>
        ((recoveryBodyStep spec base sample output entry.1).1,
          (entry.2, (recoveryBodyStep spec base sample output entry.1).2))) := by
  let actualScan := scan spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1))
    (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits)
  let fuel := ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits
  let scannedStep := scanRecord spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1)) fuel
  let packStep : Store (recoveryContext ctx modulusWidth (phaseBits + 1)) →
      Store (recoveryContext ctx modulusWidth (phaseBits + 1)) ×
        (Circuit.classical (packRecoveredOp (modulusWidth := modulusWidth) output)).Path :=
    fun initial => (initial.applyOp (packRecoveredOp (modulusWidth := modulusWidth) output), ())
  have scanEquation (reference : Register) {H : Type} [Fintype H]
      (initial : State (recoveryContext ctx modulusWidth (phaseBits + 1)) reference H) :
      actualScan.execute reference initial = initial.mapClassical (fun entry =>
        ((scannedStep entry.1).1, (entry.2, (scannedStep entry.1).2))) :=
    scanRecord_execute spec.modulusSpec
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
      (recoveryCells ctx modulusWidth (phaseBits + 1)) fuel reference initial
  have packEquation (reference : Register) {H : Type} [Fintype H]
      (initial : State (recoveryContext ctx modulusWidth (phaseBits + 1)) reference H) :
      (Circuit.classical (packRecoveredOp (modulusWidth := modulusWidth) output)).execute
          reference initial =
        initial.mapClassical (fun entry =>
          ((packStep entry.1).1, (entry.2, (packStep entry.1).2))) := by
    refine (Circuit.execute_classical_mapClassical
      (packRecoveredOp (modulusWidth := modulusWidth) output) reference initial).trans ?_
    exact mapDecision _ _ initial (fun entry =>
      ((packStep entry.1).1, (entry.2, (packStep entry.1).2)))
  let lastStep : Store (recoveryContext ctx modulusWidth (phaseBits + 1)) →
      Store (recoveryContext ctx modulusWidth (phaseBits + 1)) ×
        (Circuit.seq actualScan
          (Circuit.classical (packRecoveredOp (modulusWidth := modulusWidth) output))).Path :=
    fun initial =>
      ((packStep (scannedStep initial).1).1,
        ((scannedStep initial).2, (packStep (scannedStep initial).1).2))
  have lastEquation (reference : Register) {H : Type} [Fintype H]
      (initial : State (recoveryContext ctx modulusWidth (phaseBits + 1)) reference H) :
      (Circuit.seq actualScan
        (Circuit.classical (packRecoveredOp (modulusWidth := modulusWidth) output))).execute
          reference initial =
        initial.mapClassical (fun entry =>
          ((lastStep entry.1).1, (entry.2, (lastStep entry.1).2))) := by
    refine (Circuit.execute_seq_mapClassical actualScan
      (Circuit.classical (packRecoveredOp (modulusWidth := modulusWidth) output))
      scannedStep packStep scanEquation packEquation reference initial).trans ?_
    exact mapDecision _ _ initial (fun entry =>
      ((lastStep entry.1).1, (entry.2, (lastStep entry.1).2)))
  refine (Circuit.execute_seq_mapClassical (initializeScan ctx modulusWidth phaseBits sample)
    (Circuit.seq actualScan
      (Circuit.classical (packRecoveredOp (modulusWidth := modulusWidth) output)))
    (initializeScanStep ctx modulusWidth phaseBits sample) lastStep
    (nativeRecovery_initialize_execute ctx modulusWidth phaseBits sample) lastEquation
    Reference state).trans ?_
  exact mapDecision _ _ state (fun entry =>
    ((recoveryBodyStep spec base sample output entry.1).1,
      (entry.2, (recoveryBodyStep spec base sample output entry.1).2)))

/-- The actual outer record after all recovery workspaces have been matched and released. -/
def intoStep (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) (store : Store ctx) :
    Store ctx × (into spec base sample output).Path :=
  scopeRecoveryStep ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody spec base sample output) (recoveryBodyStep spec base sample output) store

/-- Complete native recovery follows the sole interpreter on every full reference block. -/
theorem nativeRecovery_into_execute
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into spec base sample output).execute Reference state =
      state.mapClassical (fun entry =>
        ((intoStep spec base sample output entry.1).1,
          (entry.2, (intoStep spec base sample output entry.1).2))) := by
  refine (nativeRecovery_scope_execute ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody spec base sample output) (recoveryBodyStep spec base sample output)
    (nativeRecovery_body_execute spec base sample output) Reference state).trans ?_
  exact mapDecision _ _ state (fun entry =>
    ((intoStep spec base sample output entry.1).1,
      (entry.2, (intoStep spec base sample output entry.1).2)))

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
