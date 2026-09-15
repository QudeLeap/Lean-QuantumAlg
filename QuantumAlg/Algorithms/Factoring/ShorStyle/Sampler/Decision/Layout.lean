/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Layout.Separation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.AcceptedFields
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Initialization.Readout

/-!
# The actual sampler allocation discharges decision separation

All inequalities follow from different positions in the same real eleven-cell
context. The initialization writes its default fields and preserves the
acceptance bit, modulus and zero GCD result. No separation or initialization
premise is delegated to the algorithm caller.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual fresh cells satisfy every accepted-arm separation fact without caller conditions. -/
theorem samplerLayout_accepted_separated (ctx : RuntimeCtx kind) (width : Nat) :
    Decision.AcceptedSeparated (shared ctx width) (scratch ctx width)
      (gcdResultCell ctx width) :=
  { extendedGcd := samplerLayout_cellKey_ne ctx width 7 9 (by decide)
    extendedCandidate := samplerLayout_cellKey_ne ctx width 7 8 (by decide)
    extendedUnit := samplerLayout_cellKey_ne ctx width 7 2 (by decide)
    extendedFlag := samplerLayout_cellKey_ne ctx width 7 4 (by decide)
    extendedModulus := samplerLayout_cellRead_free (modulusCell ctx width) _
      (samplerLayout_cellKey_ne ctx width 7 10 (by decide))
    gcdCandidate := samplerLayout_cellKey_ne ctx width 9 8 (by decide)
    gcdUnit := samplerLayout_cellKey_ne ctx width 9 2 (by decide)
    gcdFlag := samplerLayout_cellKey_ne ctx width 9 4 (by decide)
    positiveGcd := samplerLayout_cellKey_ne ctx width 6 9 (by decide)
    positiveCandidate := samplerLayout_cellKey_ne ctx width 6 8 (by decide)
    positiveUnit := samplerLayout_cellKey_ne ctx width 6 2 (by decide)
    positiveFlag := samplerLayout_cellKey_ne ctx width 6 4 (by decide)
    candidateUnit := samplerLayout_cellKey_ne ctx width 8 2 (by decide)
    candidateFlag := samplerLayout_cellKey_ne ctx width 8 4 (by decide)
    unitFlag := samplerLayout_cellKey_ne ctx width 2 4 (by decide) }

/-- Actual initialization supplies the candidate, wrapping one and false on arbitrary storage. -/
theorem samplerLayout_initialized_fields (store : Store (context ctx width)) :
    let final := Decision.initializationStore (shared ctx width) (scratch ctx width) store
    final.read (FirstAccepted.cellRead (candidateCell ctx width)) =
        store.read (FirstAccepted.cellRead (selectedCell ctx width)) ∧
      final.read (FirstAccepted.cellRead (selectedCell ctx width)) = CShape.wordOfNat width 1 ∧
        final.read (FirstAccepted.cellRead (eligibleCell ctx width)) = .bit false :=
  Decision.decisionInitialization_values (shared ctx width) (scratch ctx width)
    (samplerLayout_cellKey_ne ctx width 8 2 (by decide))
    (samplerLayout_cellKey_ne ctx width 4 2 (by decide))
    (samplerLayout_cellKey_ne ctx width 4 8 (by decide)) store

/-- Actual initialization preserves the three observations needed to consume the source choice. -/
theorem samplerLayout_initialization_inputs (store : Store (context ctx width)) :
    let final := Decision.initializationStore (shared ctx width) (scratch ctx width) store
    final.read (FirstAccepted.cellRead (acceptedCell ctx width)) =
        store.read (FirstAccepted.cellRead (acceptedCell ctx width)) ∧
      final.read (FirstAccepted.cellRead (modulusCell ctx width)) =
        store.read (FirstAccepted.cellRead (modulusCell ctx width)) ∧
      final.read (FirstAccepted.cellRead (gcdResultCell ctx width)) =
        store.read (FirstAccepted.cellRead (gcdResultCell ctx width)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Decision.decisionInitialization_read_other (shared ctx width) (scratch ctx width)
      (FirstAccepted.cellRead (acceptedCell ctx width))
      (samplerLayout_cellRead_free (acceptedCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 8 3 (by decide)))
      (samplerLayout_cellRead_free (acceptedCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 2 3 (by decide)))
      (samplerLayout_cellRead_free (acceptedCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 4 3 (by decide))) store
  · exact Decision.decisionInitialization_read_other (shared ctx width) (scratch ctx width)
      (FirstAccepted.cellRead (modulusCell ctx width))
      (samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 8 10 (by decide)))
      (samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 2 10 (by decide)))
      (samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 4 10 (by decide))) store
  · exact Decision.decisionInitialization_read_other (shared ctx width) (scratch ctx width)
      (FirstAccepted.cellRead (gcdResultCell ctx width))
      (samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 8 9 (by decide)))
      (samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 2 9 (by decide)))
      (samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 4 9 (by decide))) store

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout
