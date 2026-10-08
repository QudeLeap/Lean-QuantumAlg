/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import QuantumAlg.Core.Base
import QuantumAlg.Components.Oracle.BlockEncoding
import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Complement
import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Signal
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Complement

/-!
# QPP circuit construction

Internal same-circuit witnesses used by the public QPP endpoint.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open NormalizedVector Module.End

noncomputable section

variable {n : ℕ}
variable {U : UnitaryOperator (Qubits n)}

/-- Source-level synthesis data for public unitary-polynomial transformation.
Correctness and resources are both attached to the same typed circuit. -/
structure QPP.CircuitProjectedBlockWitness (L : ℕ)
    (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) where
  /-- The single typed circuit supplying both semantics and resource counts. -/
  circuit : UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout
  block_eq :
    projectedBlock 1 n
      (circuit.binaryMatrix : HilbertOperator (Qubits (1 + n)))
      = unitaryLaurentPolynomial L U coeff
  resources_exact :
    QPP.HasExactResourceCounts U (2 * L) circuit.eventCost

/-- Build the same-circuit QPP witness from an explicit QPP-evolution
certificate.  This is retained as an internal helper for source packages that
already chose a phase schedule. -/
noncomputable def QPP.qppCircuitWitnessOfEvolution
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (evolution : QPP.QppEvolutionCertificate L U coeff) :
    QPP.CircuitProjectedBlockWitness L U coeff := by
  refine
    { circuit :=
        qppAlternatingControlledCircuit U evolution.φ evolution.θ₀ evolution.φ₀
          evolution.ps
      block_eq := ?_
      resources_exact := ?_ }
  · exact evolution.block_eq
  · simpa [evolution.length_eq] using
      (qppAlternatingControlledCircuit_resources_exact U evolution.φ
        evolution.θ₀ evolution.φ₀ evolution.ps)

/-- Build the same-circuit QPP witness directly from bounded Laurent source data.
The Laurent complement gives the YZZYZ phase schedule, the source spectral
decomposition proves the projected block, and the counted typed circuit supplies
the resource profile [WZYW23, arxiv_v3.tex:635-666,2446-2465]. -/
noncomputable def QPP.qppCircuitWitnessOfBoundedLaurent
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff) :
    QPP.CircuitProjectedBlockWitness L U coeff :=
  QPP.qppCircuitWitnessOfEvolution L U coeff
    (QPP.qppEvolutionCertificateOfBoundedLaurent L U coeff h
      (QPP.phaseDecomposition U))

/-- Build the same-circuit QPP witness from the public bounded
trigonometric-polynomial hypothesis. -/
noncomputable def QPP.qppCircuitWitnessOfTrigonometricBound
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.TrigonometricPolynomialBound L coeff) :
    QPP.CircuitProjectedBlockWitness L U coeff :=
  QPP.qppCircuitWitnessOfBoundedLaurent L U coeff
    h.toBoundedLaurentPolynomial

/-- Witness-conditioned projected-block endpoint retained as an internal
helper for source packages that already choose a circuit. -/
theorem QPP.fromCircuitWitness (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.CircuitProjectedBlockWitness L U coeff) :
    ∃ circuit : UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout,
      projectedBlock 1 n
          (circuit.binaryMatrix : HilbertOperator (Qubits (1 + n)))
        = unitaryLaurentPolynomial L U coeff ∧
        QPP.HasExactResourceCounts U (2 * L) circuit.eventCost := by
  exact ⟨h.circuit, h.block_eq, h.resources_exact⟩

/-- Complement-conditioned projected-block endpoint retained as an internal
helper while the public theorem is driven by Wang's source root package. -/
theorem QPP.projectedBlock_of_boundedLaurent (L : ℕ)
    (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff) :
    ∃ circuit : UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout,
      projectedBlock 1 n
          (circuit.binaryMatrix : HilbertOperator (Qubits (1 + n)))
        = unitaryLaurentPolynomial L U coeff ∧
      QPP.HasExactResourceCounts U (2 * L) circuit.eventCost := by
  exact QPP.fromCircuitWitness L U coeff
    (QPP.qppCircuitWitnessOfBoundedLaurent L U coeff h)

/-- Public-boundedness projected-block consequence with a namespace-level name
for callers outside `QPP.Witness`. -/
theorem QPP.projectedBlock_of_trigonometricBound
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.TrigonometricPolynomialBound L coeff) :
    ∃ circuit : UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout,
      projectedBlock 1 n
          (circuit.binaryMatrix : HilbertOperator (Qubits (1 + n)))
        = unitaryLaurentPolynomial L U coeff ∧
      QPP.HasExactResourceCounts U (2 * L) circuit.eventCost := by
  exact QPP.fromCircuitWitness L U coeff
    (QPP.qppCircuitWitnessOfTrigonometricBound L U coeff h)

/-- Witness-conditioned endpoint retained as an internal helper.  Public callers
should use `QPP.Witness.main`, which derives the certificate from Wang's source
root-product package and a source spectral decomposition. -/
theorem QPP.projectedBlock_of_evolution (L : ℕ)
    (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (evolution : QPP.QppEvolutionCertificate L U coeff) :
    ∃ circuit : UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout,
      projectedBlock 1 n
          (circuit.binaryMatrix : HilbertOperator (Qubits (1 + n)))
        = unitaryLaurentPolynomial L U coeff ∧
        QPP.HasExactResourceCounts U (2 * L) circuit.eventCost := by
  exact QPP.fromCircuitWitness L U coeff
    (QPP.qppCircuitWitnessOfEvolution L U coeff evolution)

namespace QPP.Witness

/-- Namespace-local spelling of the public QPP circuit witness. -/
abbrev CircuitProjectedBlockWitness (L : ℕ)
    (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) :=
  QuantumAlg.QSP.MultiQubit.QPP.CircuitProjectedBlockWitness L U coeff

/-- Namespace-local constructor from a bounded trigonometric-polynomial
hypothesis. -/
noncomputable abbrev qppCircuitWitnessOfTrigonometricBound
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QuantumAlg.QSP.MultiQubit.QPP.TrigonometricPolynomialBound L coeff) :
    CircuitProjectedBlockWitness L U coeff :=
  QuantumAlg.QSP.MultiQubit.QPP.qppCircuitWitnessOfTrigonometricBound L U coeff h

end QPP.Witness



end

end QSP.MultiQubit

end QuantumAlg

end
