/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Space
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Complete actual initialized finite Shor resources

Actual initialization is paid once, every requested complete round is paid,
and the genuine final option encoding is paid once. All original caller
storage, five persistent heads, the single physical bank, surviving source
results and simultaneous native scratch remain in both space ledgers. Total
chronological depth counts the entire execution independently of cycle cuts.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

/-- Complete independent events of initialization, the actual finite tail and sole final pack. -/
def eventEnvelope {N : Nat} (input : Input N) (count : Nat) :
    ResourcePool (executionModel input) :=
  Initialized.readyEnvelope input + Finite.eventEnvelope input count

/-- Caller-independent allocation capacity and every retained result coexist with native scratch. -/
def additionalSpace (N count : Nat) : SpacePool .quantum :=
  Persistent.additionalSpace N + SpacePool.ofQuantumLayout (layout N) +
    Finite.additionalSpace N count

/-- Every real complete machine path pays the independent full chronological event ledger. -/
theorem code_pool_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (count : Nat) (path : (code base noQuantum N input count).Path) :
    (code base noQuantum N input count).resourcePool path ≤ eventEnvelope input count := by
  rcases path with ⟨readyPath, tailPath⟩
  change ResourcePool.ofList ((Initialized.ready base noQuantum N input).eventTrace readyPath ++
    (Finite.code (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count (Initialized.cells base noQuantum N)
      (Initialized.result base noQuantum N)).eventTrace tailPath) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (Initialized.ready_pool_eq base noQuantum N input readyPath).le
    (Finite.code_pool_le (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count (Initialized.cells base noQuantum N)
      (Initialized.result base noQuantum N) tailPath)

/-- Whole dependency depth includes the actual initializer, every round and terminal encoding. -/
theorem code_depth_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (count : Nat)
    (duration : Resource.Event (executionModel input) → Nat)
    (path : (code base noQuantum N input count).Path) :
    (code base noQuantum N input count).depth duration path ≤
      ResourcePool.weightedCount duration (eventEnvelope input count) :=
  Circuit.depth_le_weightedCount_of_pool_le (code base noQuantum N input count) duration
    (eventEnvelope input count) path (code_pool_le base noQuantum N input count path)

/-- The complete actual machine includes every real resident allocation and native workspace. -/
theorem code_resident_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (count : Nat) (path : (code base noQuantum N input count).Path) :
    (code base noQuantum N input count).peakResidentSpace path ≤
      base.residentSpace + additionalSpace N count := by
  rcases path with ⟨readyPath, tailPath⟩
  change (Circuit.seq (Initialized.ready base noQuantum N input)
    (Finite.code (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count (Initialized.cells base noQuantum N)
      (Initialized.result base noQuantum N))).peakResidentSpace ⟨readyPath, tailPath⟩ ≤ _
  rw [Circuit.peakResidentSpace_seq]
  have frame : (Initialized.bank base noQuantum N).residentSpace + Finite.additionalSpace N count =
      base.residentSpace + additionalSpace N count := by
    rw [Initialized.bank_resident]
    unfold additionalSpace
    ac_rfl
  apply SpacePool.max_le
  · exact ((Initialized.ready_resident_le base noQuantum N input readyPath).trans
      (fun axis => Nat.le_add_right _ _)).trans_eq frame
  · exact (Finite.code_resident_le (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count (Initialized.cells base noQuantum N)
      (Initialized.result base noQuantum N) tailPath).trans_eq frame

/-- The complete actual machine includes every real auxiliary allocation and native workspace. -/
theorem code_auxiliary_le (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) (count : Nat) (path : (code base noQuantum N input count).Path) :
    (code base noQuantum N input count).peakAuxiliarySpace path ≤
      base.auxiliarySpace + additionalSpace N count := by
  rcases path with ⟨readyPath, tailPath⟩
  change (Circuit.seq (Initialized.ready base noQuantum N input)
    (Finite.code (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count (Initialized.cells base noQuantum N)
      (Initialized.result base noQuantum N))).peakAuxiliarySpace ⟨readyPath, tailPath⟩ ≤ _
  rw [Circuit.peakAuxiliarySpace_seq]
  have frame : (Initialized.bank base noQuantum N).auxiliarySpace + Finite.additionalSpace N count =
      base.auxiliarySpace + additionalSpace N count := by
    rw [Initialized.bank_auxiliary]
    unfold additionalSpace
    ac_rfl
  apply SpacePool.max_le
  · exact ((Initialized.ready_auxiliary_le base noQuantum N input readyPath).trans
      (fun axis => Nat.le_add_right _ _)).trans_eq frame
  · exact (Finite.code_auxiliary_le (Initialized.bank base noQuantum N) N input
      (Initialized.bank_wires base noQuantum N) count (Initialized.cells base noQuantum N)
      (Initialized.result base noQuantum N) tailPath).trans_eq frame

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
