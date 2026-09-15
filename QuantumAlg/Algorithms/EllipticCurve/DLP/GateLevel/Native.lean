/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Layout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Attempt.Unitary
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence

/-!
# Actual literal ECDLP sampling and reuse on the original point bank

The source order expansion, including its one-term case, determines the
literal preparation. Each sample performs the original opaque group query
and inverse QFTs before measuring the actual exponent wires. Every existing
wire and finite readout cell remains live. Reuse resets and seeds those same
wires with measured classical corrections and charged basis shifts.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

/-- Prepare the original zero-exponent and identity-point basis on one actual owned bank. -/
def prepare : Circuit base (bankContext base noQuantum I) :=
  .prepare base base.canonicalFreshKey (bankLayout I) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum I) (preparation I)

/-- Allocate the bank and all original finite outcome cells exactly once. -/
def allocate : Circuit base (context base noQuantum I) :=
  (prepare base noQuantum I).seq
    (MeasurementCells.allocate (bankContext base noQuantum I) 2 (sampleWidth I))

/-- Place the original literal preparation-query-QFT circuit on its unchanged physical bank. -/
def member (B : OrderExpansion (problem I).order) (A : Access I) :
    UnitaryCircuit (context base noQuantum I).register :=
  UnitaryCircuit.reindex (basisEquiv I (nativeECDLP_context_wires base noQuantum I)).symm
    (GateLevelAttempt.quantumCircuit I B A)

/-- The actual sample preserves the complete physical footprint of the original circuit. -/
theorem nativeECDLP_member_physicalIdx (B : OrderExpansion (problem I).order) (A : Access I) :
    (member base noQuantum I B A).physical_idx = (context base noQuantum I).physicalIdx :=
  (GateLevelAttempt.quantumCircuit_physical_idx I B A).trans
    ((nativeECDLP_physicalIdx I (nativeECDLP_context_wires base noQuantum I)).trans
      (qubitLayout_systemIdx I)).symm

/-- Measure one original exponent position into its actual two-valued cell. -/
def readout (index : Fin (sampleWidth I)) : ZReadout (context base noQuantum I) where
  wire := wireEquiv I (nativeECDLP_context_wires base noQuantum I)
    ⟨index.val, by
      have bound := index.isLt
      unfold sampleWidth at bound
      unfold Layout.totalQubits
      omega⟩
  output := by
    rw [nativeECDLP_context_qubits I (nativeECDLP_context_wires base noQuantum I)]
    exact cells base noQuantum I index

/-- The two original exponent-register orders determine the real measurement sequence. -/
def readouts : List (ZReadout (context base noQuantum I)) :=
  List.ofFn (readout base noQuantum I)

/-- Original literal unitary execution is followed by real finite-outcome measurements. -/
def sample (B : OrderExpansion (problem I).order) (A : Access I) :
    Circuit (context base noQuantum I) (context base noQuantum I) :=
  (Circuit.unitary (member base noQuantum I B A)
    (nativeECDLP_member_physicalIdx base noQuantum I B A)).seq
      (Circuit.measurementSequence (readouts base noQuantum I))

private theorem sampleWidth_pos : 0 < sampleWidth I := by
  have orderPositive := (problem I).order_pos
  have widthPositive : 0 < FiniteCyclicDLP.orderWidth (problem I) := by
    apply Nat.clog_pos (by decide)
    unfold FiniteCyclicDLP.oversampledOrder FiniteCyclicDLP.fourierOversamplingFactor
    omega
  unfold sampleWidth
  omega

/-- One existing finite readout cell is reused by each sequential reset and correction. -/
def resetCell (wire : Fin (context base noQuantum I).systemCount) :
    CWriteRef (context base noQuantum I)
      (.finite ((context base noQuantum I).quantumLayout.wire wire).dimension) := by
  rw [nativeECDLP_context_qubits I (nativeECDLP_context_wires base noQuantum I)]
  exact cells base noQuantum I ⟨0, sampleWidth_pos I⟩

/-- The original identity-point basis is transported to the same live wire positions. -/
def resetLabel : (context base noQuantum I).quantumLayout.Basis :=
  (basisEquiv I (nativeECDLP_context_wires base noQuantum I)).symm (basisIndex I 0 0 1)

/-- Reset, classical correction and basis shift act on every existing original wire. -/
def reset : Circuit (context base noQuantum I) (context base noQuantum I) :=
  QuditShift.resetToBasis (resetCell base noQuantum I) (resetLabel base noQuantum I)

/-- Later samples reuse exactly the same bank and overwrite the same finite outcome cells. -/
def reusedSample (B : OrderExpansion (problem I).order) (A : Access I) :
    Circuit (context base noQuantum I) (context base noQuantum I) :=
  (reset base noQuantum I).seq (sample base noQuantum I B A)

/-- A complete single-sample run retains every wire and exposes the actual finite readouts. -/
def run (B : OrderExpansion (problem I).order) (A : Access I) :
    AlgorithmRun base (context base noQuantum I)
      (.fixedVector (sampleWidth I) (.finite 2)) where
  code := (allocate base noQuantum I).seq (sample base noQuantum I B A)
  output := Output.all (context base noQuantum I) (.read (sampleInput base noQuantum I))

/-- The sample output accounts for every original input and every surviving allocation. -/
theorem nativeECDLP_output_listing (B : OrderExpansion (problem I).order) (A : Access I) :
    (run base noQuantum I B A).output.listing = (context base noQuantum I).keys := rfl

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
