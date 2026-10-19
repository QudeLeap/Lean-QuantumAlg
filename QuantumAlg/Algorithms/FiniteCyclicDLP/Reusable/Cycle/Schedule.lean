/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Solves
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Protocol
import all QuantumAlg.Core.Algorithm.Identity
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Chronological subranges of the same sequential sample rounds

Different rounds write different retained sample cells but reuse the same
physical quantum bank. Every selected round retains its actual measurement
and full-record zero reset before the next round. An empty subrange executes
identity without a sampling round or query [Sho95, source.tex:1784-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable.Cycle

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Any prescribed chronological subrange uses the original actual round at its selected slot. -/
public def selectedRounds (P : KnownOrderProblem G) {count : Nat}
    (expansion : OrderExpansion P.order) (steps : Nat) (slots : Fin steps → Fin count) :
    QuantumAlg.Circuit (model P) (context P count) (context P count) :=
  QuantumAlg.Circuit.forRange steps (fun index => round P (slots index) expansion)

end

end QuantumAlg.FiniteCyclicDLP.Reusable.Cycle
