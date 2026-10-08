/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Borrowed
import all QuantumAlg.Components.Classical.Model.BitWord.Random.Preservation

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

variable {model : ExecutionModel}

/-- Both real result allocations restore the original complete borrowed interface. -/
theorem samplerRetained_allocation_borrowedRestored (ctx : RuntimeCtx model.kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (allocation (model := model) ctx N).BorrowedRestored Reference state
      ((allocation (model := model) ctx N).execute Reference state) := by
  exact Circuit.borrowedRestored_seq
    (Circuit.retain (model := model) ctx ctx.canonicalFreshKey (.bits (residueSamplingBits N))
      ctx.canonicalFreshKey_fresh)
    (Circuit.retain (sampleContext ctx N) (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh) state
    (Circuit.borrowedRestored_retain ctx.canonicalFreshKey (.bits (residueSamplingBits N))
      ctx.canonicalFreshKey_fresh state)
    (Circuit.borrowedRestored_retain (sampleContext ctx N).canonicalFreshKey
      (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh _)

variable [BitWord.Selected model]

/-- The actual random draw and native preparation jointly restore every borrowed correlation. -/
theorem samplerRetained_body_borrowedRestored (ctx : RuntimeCtx model.kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (body (model := model) ctx N).BorrowedRestored Reference state
      ((body (model := model) ctx N).execute Reference state) := by
  exact Circuit.borrowedRestored_seq (PackedSample.draw (model := model) N (sampleRef ctx N))
    (Program.circuit (model := model) N
      (FirstAccepted.cellRead (sampleRef ctx N)) (parameterRef ctx N)) state
    (BitWord.Random.randomCode_borrowedRestored (sampleRef ctx N) Reference state)
    (Program.samplerProgram_borrowedRestored N (FirstAccepted.cellRead (sampleRef ctx N))
      (parameterRef ctx N) Reference _)

/-- The complete retained sampler restores its original borrowed interface with every reference. -/
theorem samplerRetained_borrowedRestored (ctx : RuntimeCtx model.kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (circuit (model := model) ctx N).BorrowedRestored Reference state
      ((circuit (model := model) ctx N).execute Reference state) :=
  Circuit.borrowedRestored_seq (allocation (model := model) ctx N)
    (body (model := model) ctx N) state
    (samplerRetained_allocation_borrowedRestored (model := model) ctx N Reference state)
    (samplerRetained_body_borrowedRestored (model := model) ctx N Reference _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
