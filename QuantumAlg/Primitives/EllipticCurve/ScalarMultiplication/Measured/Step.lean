/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Placement
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement.Framing
import all QuantumAlg.Core.Execution.Context.Embedding.Permutation

/-!
# Indexed measured point steps in one complete actual context

Every step invokes the same measured point code at its selected exponent
system. Its other exponent systems remain physically resident. The actual
native embedding expresses the full union in the common entry order, allowing
successive steps to compose on exactly the same Circuit endpoints.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution

private def residentBody {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) :=
  MeasuredPointAddition.Placement.Framing.body E Q (storageMap p.size active)
    (physicalMap p.size active) (ambientContext p.size active)
    (ambient_disjoint p.size active) false

/-- Execute the indexed measured point call with every exponent and result cell resident. -/
def step {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext p.size count) (readyContext p.size count) allowAllocation :=
  Circuit.embed (ContextEmbedding.alongPermutation (framed_entries p.size active))
    (residentBody E Q active)

/-- The original point outcomes bijectively identify every complete common-context step path. -/
def stepPathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (allowAllocation : Bool := true) :
    (MeasuredPointAddition.body E Q false).Path ≃ (step E Q active allowAllocation).Path :=
  Equiv.refl _

/-- Native placement keeps the whole common context resident on every actual step path. -/
lemma step_visited {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (path : (step E Q active allowAllocation).Path) :
    (step E Q active allowAllocation).visitedContexts path = [readyContext p.size count] :=
  rfl

/-- The complete interpreter state commutes with the step's actual common entry coordinates. -/
lemma step_execute {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State ((MeasuredPointAddition.Placement.context p.size
      (storageMap p.size active) (physicalMap p.size active)).disjointUnion
        (ambientContext p.size active) (ambient_disjoint p.size active)) Reference
        (ClassicalOracleModel.empty.HiddenState × H))
    (allowAllocation : Bool := true) :
    (step E Q active allowAllocation).execute environment Reference
      (ContextPermutation.state (framed_entries p.size active) original) =
        ContextPermutation.state (framed_entries p.size active)
          ((residentBody E Q active).execute environment Reference original) :=
  Circuit.permutation_embed_execute (environment := environment) (framed_entries p.size active)
    (residentBody E Q active) Reference original

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
