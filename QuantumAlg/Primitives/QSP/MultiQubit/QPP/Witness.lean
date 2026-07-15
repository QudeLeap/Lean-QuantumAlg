/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Complement

/-!
# QPP public witness

Same-circuit public QPP witness and endpoint theorem.
-/

@[expose] public section

namespace QuantumAlg

namespace QSP.MultiQubit

open PureState Module.End

noncomputable section

variable {n : ℕ}
variable {U : Gate (Qubits n)}

/-- Source-level synthesis data for public unitary-polynomial transformation.
Correctness and resources are both attached to the same typed circuit. -/
structure QPP.CircuitProjectedBlockWitness (L : ℕ) (U : Gate (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) where
  /-- Gate-level circuit used in the projected-block equality. -/
  circuit : Gate (Qubits (1 + n))
  /-- Typed circuit carrying the trusted resource counters. -/
  typedCircuit : Circuit (Qubits (1 + n))
  circuit_eq_typed_matrix :
    (circuit : HilbertOperator (Qubits (1 + n))) =
      (show HilbertOperator (Qubits (1 + n)) from
        (typedCircuit.matrix : HilbertOperator (Qubits (1 + n))))
  block_eq :
    projectedBlock 1 n
      (show HilbertOperator (Qubits (1 + n)) from
        (typedCircuit.matrix : HilbertOperator (Qubits (1 + n))))
      = unitaryLaurentPolynomial L U coeff
  resources_exact :
    ResourceProfile.HasExactCounts typedCircuit.resources (2 * L) 0 (4 * L + 3) 0

/-- Build the same-circuit QPP witness from an explicit QPP-evolution
certificate.  This is retained as an internal helper for source packages that
already chose a phase schedule. -/
noncomputable def QPP.qppCircuitWitnessOfEvolution
    (L : ℕ) (U : Gate (Qubits n)) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff)
    (evolution : QPP.QppEvolutionCertificate L U coeff) :
    QPP.CircuitProjectedBlockWitness L U coeff := by
  classical
  let _projection := QPP.trigonometricQSPProjection_exists L coeff h
  refine
    { circuit := qppAlternatingControlledGate U evolution.φ evolution.θ₀ evolution.φ₀ evolution.ps
      typedCircuit :=
        qppAlternatingControlledCircuit U evolution.φ evolution.θ₀ evolution.φ₀
          evolution.ps
      circuit_eq_typed_matrix := ?_
      block_eq := ?_
      resources_exact := ?_ }
  · exact (qppAlternatingControlledCircuit_matrix U evolution.φ evolution.θ₀ evolution.φ₀
      evolution.ps).symm
  · simpa using evolution.block_eq
  · rcases qppAlternatingControlledCircuit_resources_exact U evolution.φ evolution.θ₀
      evolution.φ₀ evolution.ps with
      ⟨horacle, hhadamard, helementary, hclassical⟩
    refine ⟨?_, hhadamard, ?_, hclassical⟩
    · simpa [evolution.length_eq] using horacle
    · rw [helementary, evolution.length_eq]
      omega

/-- Build the same-circuit QPP witness directly from bounded Laurent source data.
The Laurent complement gives the YZZYZ phase schedule, the source spectral
decomposition proves the projected block, and the counted typed circuit supplies
the resource profile [WZYW23, arxiv_v3.tex:635-666,2446-2465]. -/
noncomputable def QPP.qppCircuitWitnessOfBoundedLaurent
    (L : ℕ) (U : Gate (Qubits n)) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff) :
    QPP.CircuitProjectedBlockWitness L U coeff :=
  QPP.qppCircuitWitnessOfEvolution L U coeff h
    (QPP.qppEvolutionCertificateOfBoundedLaurent L U coeff h
      (QPP.phaseDecomposition U))

/-- Build the same-circuit QPP witness from the public bounded
trigonometric-polynomial hypothesis. -/
noncomputable def QPP.qppCircuitWitnessOfTrigonometricBound
    (L : ℕ) (U : Gate (Qubits n)) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.TrigonometricPolynomialBound L coeff) :
    QPP.CircuitProjectedBlockWitness L U coeff :=
  QPP.qppCircuitWitnessOfBoundedLaurent L U coeff
    h.toBoundedLaurentPolynomial

/-- Compatibility spelling for the source-bounded constructor retained by the
shared QML API. -/
noncomputable def QPP.qppCircuitWitnessOfSourceBoundedLaurent
    (L : ℕ) (U : Gate (Qubits n)) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.TrigonometricPolynomialBound L coeff) :
    QPP.CircuitProjectedBlockWitness L U coeff :=
  QPP.qppCircuitWitnessOfTrigonometricBound L U coeff h

/-- Witness-conditioned projected-block endpoint retained as an internal
helper for source packages that already choose a circuit. -/
theorem QPP.fromCircuitWitness (L : ℕ) (U : Gate (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.CircuitProjectedBlockWitness L U coeff) :
    ∃ circuit : Circuit (Qubits (1 + n)),
      projectedBlock 1 n
          (show HilbertOperator (Qubits (1 + n)) from
            (circuit.matrix : HilbertOperator (Qubits (1 + n))))
        = unitaryLaurentPolynomial L U coeff ∧
        ResourceProfile.HasExactCounts circuit.resources (2 * L) 0 (4 * L + 3) 0 := by
  exact ⟨h.typedCircuit, h.block_eq, h.resources_exact⟩

/-- Complement-conditioned projected-block endpoint retained as an internal
helper while the public theorem is driven by Wang's source root package. -/
theorem QPP.projectedBlock_of_boundedLaurent (L : ℕ) (U : Gate (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff) :
    ∃ circuit : Circuit (Qubits (1 + n)),
      projectedBlock 1 n
          (show HilbertOperator (Qubits (1 + n)) from
            (circuit.matrix : HilbertOperator (Qubits (1 + n))))
        = unitaryLaurentPolynomial L U coeff ∧
      ResourceProfile.HasExactCounts
          circuit.resources (2 * L) 0 (4 * L + 3) 0 := by
  exact QPP.fromCircuitWitness L U coeff
    (QPP.qppCircuitWitnessOfBoundedLaurent L U coeff h)

namespace QPP.Witness

/-- **Unitary polynomial transformation** [WZYW23, arxiv_v3.tex:635-666,
2237-2274,2446-2465].  The bounded trigonometric-polynomial hypothesis supplies
the Laurent complement internally; the source spectral decomposition of `U`
turns the same counted QPP circuit into the projected-block operator identity. -/
theorem main
    (L : ℕ) (U : Gate (Qubits n)) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.TrigonometricPolynomialBound L coeff) :
    ∃ circuit : Circuit (Qubits (1 + n)),
      projectedBlock 1 n
          (show HilbertOperator (Qubits (1 + n)) from
            (circuit.matrix : HilbertOperator (Qubits (1 + n))))
        = unitaryLaurentPolynomial L U coeff ∧
      ResourceProfile.HasExactCounts circuit.resources (2 * L) 0 (4 * L + 3) 0 := by
  exact QPP.fromCircuitWitness L U coeff
    (QPP.qppCircuitWitnessOfTrigonometricBound L U coeff h)

end QPP.Witness

/-- Public-boundedness projected-block consequence with a namespace-level name
for callers outside `QPP.Witness`. -/
theorem QPP.projectedBlock_of_trigonometricBound
    (L : ℕ) (U : Gate (Qubits n)) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.TrigonometricPolynomialBound L coeff) :
    ∃ circuit : Circuit (Qubits (1 + n)),
      projectedBlock 1 n
          (show HilbertOperator (Qubits (1 + n)) from
            (circuit.matrix : HilbertOperator (Qubits (1 + n))))
        = unitaryLaurentPolynomial L U coeff ∧
      ResourceProfile.HasExactCounts
        circuit.resources (2 * L) 0 (4 * L + 3) 0 := by
  exact QPP.Witness.main L U coeff h

/-- Witness-conditioned endpoint retained as an internal helper.  Public callers
should use `QPP.Witness.main`, which derives the certificate from Wang's source
root-product package and a source spectral decomposition. -/
theorem QPP.projectedBlock_of_evolution (L : ℕ) (U : Gate (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff)
    (evolution : QPP.QppEvolutionCertificate L U coeff) :
    ∃ circuit : Circuit (Qubits (1 + n)),
      projectedBlock 1 n
          (show HilbertOperator (Qubits (1 + n)) from
            (circuit.matrix : HilbertOperator (Qubits (1 + n))))
        = unitaryLaurentPolynomial L U coeff ∧
        ResourceProfile.HasExactCounts
          circuit.resources (2 * L) 0 (4 * L + 3) 0 := by
  exact QPP.fromCircuitWitness L U coeff
    (QPP.qppCircuitWitnessOfEvolution L U coeff h evolution)

/-- Resource-correct public witness for unitary polynomial transformation:
the circuit witness is promoted directly from the counted QPP word used in the
projected-block equality. -/
def QPP.mainResourceCorrectWitness (L : ℕ) (U : Gate (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.TrigonometricPolynomialBound L coeff) :
    ResourceCorrectWitness (R := Qubits (1 + n))
      (∃ circuit : Circuit (Qubits (1 + n)),
        projectedBlock 1 n
            (show HilbertOperator (Qubits (1 + n)) from
              (circuit.matrix : HilbertOperator (Qubits (1 + n))))
          = unitaryLaurentPolynomial L U coeff ∧
          ResourceProfile.HasExactCounts
            circuit.resources (2 * L) 0 (4 * L + 3) 0)
      (ResourceProfile.HasExactCounts
            (QPP.qppCircuitWitnessOfTrigonometricBound L U coeff h).typedCircuit.resources
            (2 * L) 0 (4 * L + 3) 0) := by
  let witness := QPP.qppCircuitWitnessOfTrigonometricBound L U coeff h
  exact
    { circuit := witness.typedCircuit
      correctness := QPP.Witness.main L U coeff h
      resources := witness.resources_exact }

namespace QPP.Witness

/-- Namespace-local spelling of the public QPP circuit witness. -/
abbrev CircuitProjectedBlockWitness (L : ℕ) (U : Gate (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) :=
  QuantumAlg.QSP.MultiQubit.QPP.CircuitProjectedBlockWitness L U coeff

/-- Namespace-local constructor from a bounded trigonometric-polynomial
hypothesis. -/
noncomputable abbrev qppCircuitWitnessOfTrigonometricBound
    (L : ℕ) (U : Gate (Qubits n)) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QuantumAlg.QSP.MultiQubit.QPP.TrigonometricPolynomialBound L coeff) :
    CircuitProjectedBlockWitness L U coeff :=
  QuantumAlg.QSP.MultiQubit.QPP.qppCircuitWitnessOfTrigonometricBound L U coeff h

/-- Namespace-local resource-correct QPP witness. -/
abbrev mainResourceCorrectWitness (L : ℕ) (U : Gate (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QuantumAlg.QSP.MultiQubit.QPP.TrigonometricPolynomialBound L coeff) :=
  QuantumAlg.QSP.MultiQubit.QPP.mainResourceCorrectWitness L U coeff h

end QPP.Witness



end

end QSP.MultiQubit

end QuantumAlg
