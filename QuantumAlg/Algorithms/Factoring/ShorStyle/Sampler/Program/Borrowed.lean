/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scope.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Borrowed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Borrowed
import all QuantumAlg.Components.Classical.ConstantWord.Preservation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Projection

/-!
# Complete borrowed restoration of the actual scoped sampler

The literal loader, proposal fold and decision preserve all borrowed store
values. The eleven actual allocations and releases retain those same values.
Together with the exact execution equation this restores all borrowed
classical and quantum systems jointly with every external reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private theorem pop_borrowed (width : Nat) (store : Store (Layout.context ctx width)) :
    (Layout.popStore width store).readBorrowedClassical = store.readBorrowedClassical := rfl

private theorem push_borrowed (width : Nat) (store : Store ctx) :
    (Layout.pushStore width store).readBorrowedClassical = store.readBorrowedClassical := rfl

/-- The literal modulus loader and ordered scan preserve every borrowed classical value. -/
theorem samplerScan_borrowed_values (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (store : Store (Layout.context ctx (modulusBits N))) :
    (Scan.step N sample store).1.readBorrowedClassical = store.readBorrowedClassical := by
  exact (Proposal.proposalFold_borrowed_values (Layout.underRead sample (modulusBits N))
    (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))
    (List.ofFn (fun proposal : Fin residueProposalCount => proposal))
    (Scan.loaderStep N store).1).trans
      (ConstantWord.constantWord_foldStep_borrowed_values
        (Layout.modulusCell ctx (modulusBits N))
        (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) store)

/-- The complete actual inner program keeps the entire borrowed classical readout. -/
theorem samplerInner_borrowed_values (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (store : Store (Layout.context ctx (modulusBits N))) :
    (innerStep N sample output store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  exact (Decision.decision_borrowed_values (Layout.shared ctx (modulusBits N))
    (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
    (Layout.underWrite output (modulusBits N)) (Scan.step N sample store).1).trans
      (samplerScan_borrowed_values N sample store)

/-- Entering and leaving the eleven real scopes changes no borrowed classical value. -/
theorem samplerProgram_borrowed_values (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (store : Store ctx) :
    (step N sample output store).1.readBorrowedClassical = store.readBorrowedClassical := by
  refine (congrArg (fun current : Store ctx => current.readBorrowedClassical)
    (samplerProgram_store_projection N sample output store)).trans ?_
  let final := (innerStep N sample output (Layout.pushStore (modulusBits N) store)).1
  have exited : (Layout.popStore (modulusBits N) final).readBorrowedClassical =
      final.readBorrowedClassical := pop_borrowed (modulusBits N) final
  have entered : (Layout.pushStore (modulusBits N) store).readBorrowedClassical =
      store.readBorrowedClassical := push_borrowed (modulusBits N) store
  exact exited.trans ((samplerInner_borrowed_values N sample output
    (Layout.pushStore (modulusBits N) store)).trans entered)

/-- The actual sampler restores borrowed systems with arbitrary external-reference coherence. -/
theorem samplerProgram_borrowedRestored (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (circuit N sample output).BorrowedRestored Reference state
      ((circuit N sample output).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, samplerProgram_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := History) (K := History × (circuit N sample output).Path) state
    (fun entry => ((step N sample output entry.1).1,
      (entry.2, (step N sample output entry.1).2)))
    (fun entry => samplerProgram_borrowed_values N sample output entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
