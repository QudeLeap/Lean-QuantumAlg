/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Results
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Frame
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs

/-!
# One actual P-256 window bank and its retained Fourier results

The caller supplies no quantum systems. One prepareZero instruction allocates
the canonical 854-system point-and-address bank. The following retain
instructions allocate all 520 binary measurement results before sampling.
The borrowed public input cells remain in the same runtime context.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

private lemma bankDisjoint (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) :
    List.Disjoint (QubitLayout.canonical encoding.width).toQuantum.identities
      base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- The one complete physical bank, with all original classical cells retained. -/
def bankContext : RuntimeCtx .quantum :=
  base.addOwnedLayout base.canonicalFreshKey
    (QubitLayout.canonical encoding.width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum)

/-- Both full Fourier streams keep distinct real binary result cells. -/
def resultContext : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum) 2 520

/-- Actual preparation from a quantum-empty caller to the complete measured bank. -/
def prepare {services : ClassicalOracleModel} :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      base (resultContext base noQuantum) :=
  (Circuit.prepareZero base base.canonicalFreshKey
    (QubitLayout.canonical encoding.width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum)).seq
      (allocate (services := services) (bankContext base noQuantum))

/-- The retained result ports refer to the cells allocated by prepare. -/
def preparedResults : Fourier.Results (resultContext base noQuantum) :=
  results (bankContext base noQuantum)

/-- Each original borrowed P or Q read survives both real allocations. -/
def originalInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (resultContext base noQuantum) shape :=
  MeasurementCells.liftInput 2
    (input.underOwnedLayout base.canonicalFreshKey
      (QubitLayout.canonical encoding.width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum)) 520

lemma resultContext_wires :
    (QubitLayout.canonical encoding.width).toQuantum.wires =
      (resultContext base noQuantum).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, resultContext,
    MeasurementCells.context_quantumWires]
  change (QubitLayout.canonical encoding.width).toQuantum.wires =
    (QubitLayout.canonical encoding.width).toQuantum.wires ++ base.quantumWires
  rw [noQuantum, List.append_nil]

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
