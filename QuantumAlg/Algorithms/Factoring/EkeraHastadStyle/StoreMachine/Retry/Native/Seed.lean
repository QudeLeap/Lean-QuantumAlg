/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Seed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Seed
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# The actual finite recovered-batch chain retains its complete bank seed

Induction follows the real same-bank suffix and its exact history
reassociation. The first batch establishes the seed without an incoming
promise; every later batch preserves it in each complete store-reference
block. The borrowed-wire condition follows internally from the empty
incoming quantum boundary and the actual owned-allocation semantics.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

noncomputable section

open Execution ShortDLP.CompiledMAU

variable {N : Nat}

/-- The complete actual suffix preserves the seed in every complete final store-reference block. -/
theorem suffix_seedBlocks (input : Input N) (count : Nat) (start : RuntimeCtx .quantum)
    (wires : start.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
    (originalCells : Fin (measurementBits N) → CWriteRef start (.finite 2))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State start Reference (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      wires N state) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      ((suffixWires N start count).trans wires) N
      ((suffixCode input start wires originalCells count).execute Reference state) := by
  induction count generalizing start History with
  | zero =>
      exact BasisSeeded.mapHistory _ state.skip
        (BasisSeeded.mapHistory _ state seeded (fun record => (record, ())))
        (fun record => (record.1.1, (record.1.2, record.2)))
  | succ count induction =>
      let next := NativeBatchReuseRecovery.context start N
      let nextWires := (NativeBatchReuseRecovery.context_base_wires start N).trans wires
      let nextCells := fun index => reuseWrite N (originalCells index)
      let first := NativeBatchReuseRecovery.code start wires originalCells input
      let rest := suffixCode input next nextWires nextCells count
      have advanced := NativeBatchReuseRecovery.code_seedBlocks start wires originalCells
        input state seeded
      have continued := induction next nextWires nextCells (first.execute Reference state) advanced
      exact BasisSeeded.seq first rest
        ((RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
          ((suffixWires N next count).trans nextWires)).symm
          (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) state continued

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The actual chain establishes its final complete seed without a caller seed premise. -/
theorem code_seedBlocks (input : Input N) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History)) :
    RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (sameWires base noQuantum N count) N
      ((code base noQuantum input count).execute Reference state) := by
  have first := NativeBatchRecovery.code_seedBlocks base noQuantum input state
  have continued := suffix_seedBlocks input count (NativeBatchRecovery.context base noQuantum N)
    (firstWires base noQuantum N) (firstCells base noQuantum N)
    ((NativeBatchRecovery.code base noQuantum input).execute Reference state) first
  exact BasisSeeded.seq (NativeBatchRecovery.code base noQuantum input)
    (suffixCode input (NativeBatchRecovery.context base noQuantum N)
      (firstWires base noQuantum N) (firstCells base noQuantum N) count)
    ((RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (sameWires base noQuantum N count)).symm
      (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) state continued

/-- All final quantum storage belongs to the one actual owned first-batch bank. -/
theorem context_noBorrowedQuantum (input : Input N) (count : Nat) :
    (context base noQuantum N count).borrowedQuantumWires = [] := by
  have empty : base.borrowedQuantumWires = [] := by
    have subset := base.borrowedQuantumWires_sublist
    rw [noQuantum] at subset
    exact List.sublist_nil.mp subset
  exact (code base noQuantum input count).borrowedQuantumWires_preserved.trans empty

/-- The complete actual chain restores every borrowed classical-reference correlation. -/
theorem code_borrowedRestored (input : Input N) (count : Nat) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History)) :
    (code base noQuantum input count).BorrowedRestored Reference state
      ((code base noQuantum input count).execute Reference state) := by
  have empty : base.borrowedQuantumWires = [] := by
    have subset := base.borrowedQuantumWires_sublist
    rw [noQuantum] at subset
    exact List.sublist_nil.mp subset
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (code base noQuantum input count) empty Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain
