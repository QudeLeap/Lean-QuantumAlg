/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence

/-!
# Final-Store observations of the same complete source run

The return type is a scalar, so a proved equality of whole stage lists can
be used without changing their dependent history carriers. The underlying
run still retains the original Store, service state and every measured Path.
Only the observable ignores the mathematical history coordinates.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

namespace Stage

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference : Register}

/-- Final-Store weight of the literal complete source run. -/
def storeWeight
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (stages : List (Stage ctx operations services Reference))
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (effects : Store ctx → Effect (ctx.register.prod Reference)) : Real :=
  (run environment stages state).effectWeight (fun record => effects record.1)

/-- The same exact source observation pulls back this final-Store weight. -/
lemma window_sourceSequence_storeWeight
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (stages : List (Stage ctx operations services Reference))
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (effects : Store ctx → Effect (ctx.register.prod Reference)) :
    storeWeight environment stages state effects =
      state.effectWeight (observation environment stages (fun record => effects record.1)) :=
  window_sourceSequence_weight environment stages state (fun record => effects record.1)

end Stage

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
