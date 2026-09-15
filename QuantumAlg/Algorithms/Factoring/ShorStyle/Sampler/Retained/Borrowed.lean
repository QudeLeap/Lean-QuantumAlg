/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Borrowed
import all QuantumAlg.Core.Execution.Random.Borrowed

/-!
# Complete borrowed restoration of the actual retained sampler

The two real retained allocations, independent random-bit draw and expanded
scoped preparation each preserve the original borrowed interface. Their
actual sequential execution therefore restores every borrowed value and its
joint quantum-reference correlations, for every incoming state and history.
The source sample and full parameter remain as real retained outputs.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind}

/-- Both real result allocations restore the original complete borrowed interface. -/
theorem samplerRetained_allocation_borrowedRestored (ctx : RuntimeCtx kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (allocation ctx N).BorrowedRestored Reference state
      ((allocation ctx N).execute Reference state) := by
  exact Circuit.borrowedRestored_seq
    (Circuit.retain ctx ctx.canonicalFreshKey (.bits (residueSamplingBits N))
      ctx.canonicalFreshKey_fresh)
    (Circuit.retain (sampleContext ctx N) (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh) state
    (Circuit.borrowedRestored_retain ctx.canonicalFreshKey (.bits (residueSamplingBits N))
      ctx.canonicalFreshKey_fresh state)
    (Circuit.borrowedRestored_retain (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh _)

/-- The actual random draw and native preparation jointly restore every borrowed correlation. -/
theorem samplerRetained_body_borrowedRestored (ctx : RuntimeCtx kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (body ctx N).BorrowedRestored Reference state
      ((body ctx N).execute Reference state) := by
  exact Circuit.borrowedRestored_seq (PackedSample.draw N (sampleRef ctx N))
    (Program.circuit N (FirstAccepted.cellRead (sampleRef ctx N)) (parameterRef ctx N)) state
    (Circuit.borrowedRestored_randomBits (residueSamplingBits N) (sampleRef ctx N) state)
    (Program.samplerProgram_borrowedRestored N (FirstAccepted.cellRead (sampleRef ctx N))
      (parameterRef ctx N) Reference _)

/-- The complete retained sampler restores its original borrowed interface with every reference. -/
theorem samplerRetained_borrowedRestored (ctx : RuntimeCtx kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (circuit ctx N).BorrowedRestored Reference state
      ((circuit ctx N).execute Reference state) :=
  Circuit.borrowedRestored_seq (allocation ctx N) (body ctx N) state
    (samplerRetained_allocation_borrowedRestored ctx N Reference state)
    (samplerRetained_body_borrowedRestored ctx N Reference _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
