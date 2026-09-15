/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Placement
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement.Framing
import all QuantumAlg.Core.Execution.Context.Permutation.Local.State

/-!
# Indexed measured point steps in one complete actual context

Every step invokes the same measured point code at its selected exponent
system. Its other exponent systems remain physically resident. The actual
local compiler expresses the full union in the common entry order, allowing
successive steps to compose on exactly the same Circuit endpoints.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

private def residentBody {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) :=
  MeasuredPointAddition.Placement.Framing.body E Q (storageMap p.size active)
    (physicalMap p.size active) (ambientContext p.size active) (ambient_disjoint p.size active)

private theorem residentBody_local {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) : (residentBody E Q active).IsLocal :=
  MeasuredPointAddition.Placement.Framing.body_isLocal E Q (storageMap p.size active)
    (physicalMap p.size active) (ambientContext p.size active) (ambient_disjoint p.size active)

/-- Execute the indexed measured point call with every exponent and result cell resident. -/
def step {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) :
    Circuit (readyContext p.size count) (readyContext p.size count) :=
  ContextPermutation.localCircuit (residentBody E Q active) (residentBody_local E Q active)
    (readyContext p.size count) (framed_entries p.size active)

/-- The common-context step retains the same actual local instructions. -/
theorem step_isLocal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) : (step E Q active).IsLocal :=
  ContextPermutation.localCircuit_isLocal (residentBody E Q active) (residentBody_local E Q active)
    (readyContext p.size count) (framed_entries p.size active)

/-- The original point outcomes bijectively identify every complete common-context step path. -/
def stepPathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) :
    (MeasuredPointAddition.body E Q).Path ≃ (step E Q active).Path :=
  (MeasuredPointAddition.Placement.Framing.pathEquiv E Q (storageMap p.size active)
    (physicalMap p.size active) (ambientContext p.size active)
    (ambient_disjoint p.size active)).trans
      (ContextPermutation.localPathEquiv (residentBody E Q active) (residentBody_local E Q active)
        (readyContext p.size count) (framed_entries p.size active))

/-- The complete interpreter state commutes with the step's actual common entry coordinates. -/
theorem step_execute {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State ((MeasuredPointAddition.Placement.context p.size
      (storageMap p.size active) (physicalMap p.size active)).disjointUnion
        (ambientContext p.size active) (ambient_disjoint p.size active)) Reference H) :
    (step E Q active).execute Reference
      (ContextPermutation.state (framed_entries p.size active) original) =
        (ContextPermutation.state (framed_entries p.size active)
          ((residentBody E Q active).execute Reference original)).mapHistory
            (fun record => (record.1, ContextPermutation.localPathEquiv
              (residentBody E Q active) (residentBody_local E Q active)
              (readyContext p.size count) (framed_entries p.size active) record.2)) :=
  ContextPermutation.localCircuit_execute (residentBody E Q active) (residentBody_local E Q active)
    (readyContext p.size count) (framed_entries p.size active) Reference original

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
