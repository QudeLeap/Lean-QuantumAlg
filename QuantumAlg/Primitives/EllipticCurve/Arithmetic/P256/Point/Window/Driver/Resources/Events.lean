/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Resources.Events
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Scope.Quantum.Events

/-!
# Independent complete native pool for an actual constructed-table point action

The full original five-table builder and the same six-query measured point
program both contribute their independent finite allowances. Only static
window widths and the public field modulus occur in this specification.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open ClassicalAlgorithms.Modular

noncomputable section

attribute [local irreducible] Circuit.resourcePool Chain.Program.Parameters.circuit

/-- Independent full native allowance for one actual table-building point operation. -/
def eventEnvelope (services : ClassicalOracleModel) (spec : ModulusSpec 256)
    (highRemaining lowWidth : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  ClassicalRoutines.EllipticCurve.WindowTables.TableFrame.envelope
    (.quantum AlgorithmGate.model .empty BitWord.model services)
    (highRemaining + lowWidth + 1) spec +
      Chain.Program.Parameters.eventEnvelope services highRemaining lowWidth

/-- Every original driver path pays its full table builder and same-path point operation. -/
lemma Parameters.circuit_pool_le {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame ctx 256)
    (spec : ModulusSpec 256) (row : Fin 34)
    (path : (circuit (services := services) parameters frame spec row).Path) :
    (circuit parameters frame spec row).resourcePool path ≤
      eventEnvelope services spec parameters.highRemaining parameters.lowWidth := by
  unfold circuit at path ⊢
  unfold eventEnvelope
  apply frame.withConstructedQuantumTables_pool_le
    (gates := AlgorithmGate.model) (oracles := .empty) (operations := BitWord.model)
    (services := services) spec row _
    (Chain.Program.Parameters.eventEnvelope services parameters.highRemaining parameters.lowWidth)
  intro inner lift same table selected
  exact (kernelParameters parameters lift same table.arrays).circuit_pool_le selected

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver
