/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition

/-!
# Hermitian QSVT endpoints

Hermitian block-encoding endpoints derived from projected QSVT.
-/

@[expose] public section

namespace QuantumAlg

namespace QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder
open ReflectionQSPPhaseSynthesis

namespace QSVT

/-- Resource counters for Hermitian block-encoding QSVT constructions. -/
structure HermitianResourceProfile where
  /-- Trusted count of base block-encoding oracle queries. -/
  oracleQueries : ℕ
  /-- Trusted count of controlled-oracle queries. -/
  controlledOracleQueries : ℕ
  /-- Ancilla qubits used by the Hermitian QSVT construction. -/
  ancillaQubits : ℕ
  /-- Trusted count of elementary gates outside oracle calls. -/
  elementaryGates : ℕ
deriving DecidableEq

namespace HermitianResourceProfile

/-- Exact counter claim for Hermitian QSVT resource profiles. -/
def HasExactCounts (profile : HermitianResourceProfile)
    (oracleQueries controlledOracleQueries ancillaQubits elementaryGates : ℕ) : Prop :=
  profile.oracleQueries = oracleQueries ∧
    profile.controlledOracleQueries = controlledOracleQueries ∧
    profile.ancillaQubits = ancillaQubits ∧
    profile.elementaryGates = elementaryGates

/-- The portion of a Hermitian QSVT resource profile represented by the generic
typed-circuit counters.  Controlled-oracle and ancilla counts remain in the
Hermitian-specific profile. -/
def toCircuitResourceProfile (profile : HermitianResourceProfile) : ResourceProfile where
  oracleQueries := profile.oracleQueries
  hadamardGates := 0
  elementaryGates := profile.elementaryGates
  classicalOps := 0

theorem toCircuitResourceProfile_exact (profile : HermitianResourceProfile) :
    ResourceProfile.HasExactCounts profile.toCircuitResourceProfile
      profile.oracleQueries 0 profile.elementaryGates 0 := by
  simp [toCircuitResourceProfile, ResourceProfile.HasExactCounts]

end HermitianResourceProfile

/-- Resource target for the real matching-parity Hermitian QSVT specialization:
`L` uses of `U`/`U†`, one extra ancilla qubit, and `(m+1)L` elementary gates. -/
def realParityResources (m L : ℕ) : HermitianResourceProfile where
  oracleQueries := L
  controlledOracleQueries := 0
  ancillaQubits := 1
  elementaryGates := (m + 1) * L

/-- Resource target for the shared-control complex Hermitian QSVT support shape:
linear ordinary queries, one controlled-`U`, two extra ancilla qubits, and
`(m+1)L` elementary gates. -/
def hermitianComplexResources (m L : ℕ) : HermitianResourceProfile where
  oracleQueries := L
  controlledOracleQueries := 1
  ancillaQubits := 2
  elementaryGates := (m + 1) * L

/-- Conservative public resource target for the complex Hermitian QSVT
specialization proved in this module.

The public endpoint uses the source-supported four-real-branch construction:
real/imaginary and even/odd branches are synthesized separately and combined by
selector block encodings.  This keeps the statement honest with three extra
ancillas and constant-factor overheads in the same asymptotic classes. -/
def hermitianComplexFourBranchResources (m L : ℕ) : HermitianResourceProfile where
  oracleQueries := 4 * L
  controlledOracleQueries := 4
  ancillaQubits := 3
  elementaryGates := 4 * ((m + 1) * L)

theorem realParityResources_exact (m L : ℕ) :
    HermitianResourceProfile.HasExactCounts
      (realParityResources m L) L 0 1 ((m + 1) * L) := by
  simp [HermitianResourceProfile.HasExactCounts, realParityResources]

theorem hermitianComplexResources_exact (m L : ℕ) :
    HermitianResourceProfile.HasExactCounts
      (hermitianComplexResources m L) L 1 2 ((m + 1) * L) := by
  simp [HermitianResourceProfile.HasExactCounts, hermitianComplexResources]

theorem hermitianComplexFourBranchResources_exact (m L : ℕ) :
    HermitianResourceProfile.HasExactCounts
      (hermitianComplexFourBranchResources m L)
      (4 * L) 4 3 (4 * ((m + 1) * L)) := by
  simp [HermitianResourceProfile.HasExactCounts, hermitianComplexFourBranchResources]

theorem realParityOracleQueries_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (realParityResources m L).oracleQueries)
      (fun L : ℕ => L) := by
  simpa [NatBigO, realParityResources, Function.id_def] using
    (NatBigO.refl (fun L : ℕ => L))

theorem hermitianComplexOracleQueries_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (hermitianComplexResources m L).oracleQueries)
      (fun L : ℕ => L) := by
  simpa [NatBigO, hermitianComplexResources, Function.id_def] using
    (NatBigO.refl (fun L : ℕ => L))

theorem hermitianComplexFourBranchOracleQueries_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (hermitianComplexFourBranchResources m L).oracleQueries)
      (fun L : ℕ => L) := by
  simpa [hermitianComplexFourBranchResources] using
    (NatBigO.const_mul_left 4 (fun L : ℕ => L))

theorem realParityElementaryGates_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (realParityResources m L).elementaryGates)
      (fun L : ℕ => (m + 1) * L) := by
  simpa [NatBigO, realParityResources] using
    (NatBigO.refl (fun L : ℕ => (m + 1) * L))

theorem hermitianComplexElementaryGates_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (hermitianComplexResources m L).elementaryGates)
      (fun L : ℕ => (m + 1) * L) := by
  simpa [NatBigO, hermitianComplexResources] using
    (NatBigO.refl (fun L : ℕ => (m + 1) * L))

theorem hermitianComplexFourBranchElementaryGates_bigO (m : ℕ) :
    NatBigO (fun L : ℕ => (hermitianComplexFourBranchResources m L).elementaryGates)
      (fun L : ℕ => (m + 1) * L) := by
  simpa [hermitianComplexFourBranchResources] using
    (NatBigO.const_mul_left 4 (fun L : ℕ => (m + 1) * L))

theorem realParityAncillaQubits_exact (m L : ℕ) :
    (realParityResources m L).ancillaQubits = 1 := rfl

theorem hermitianComplexAncillaQubits_exact (m L : ℕ) :
    (hermitianComplexResources m L).ancillaQubits = 2 := rfl

theorem hermitianComplexFourBranchAncillaQubits_exact (m L : ℕ) :
    (hermitianComplexFourBranchResources m L).ancillaQubits = 3 := rfl

theorem hermitianComplexControlledQueries_exact (m L : ℕ) :
    (hermitianComplexResources m L).controlledOracleQueries = 1 := rfl

theorem hermitianComplexFourBranchControlledQueries_exact (m L : ℕ) :
    (hermitianComplexFourBranchResources m L).controlledOracleQueries = 4 := rfl

/-! ### Hermitian QSVT endpoint contracts -/

/-- A lightweight source-level Hermitian QSVT gate word.

The `signal` field is the source block-encoding oracle, `output` is the
constructed output gate whose projected block is proved below, and `resources`
records the trusted query and elementary-gate counters used by the public
theorem nodes.  The certificate also keeps the source block-encoding proof and
the public total-ancilla accounting (`m` source ancillas plus `a` transformation
ancillas) with the word, so the endpoint theorems cannot silently forget the
input oracle. -/
structure HermitianQSVTWord (m a n : Nat) (A : HilbertOperator (Qubits n)) where
  /-- Source block-encoding oracle used as the Hermitian QSVT signal. -/
  signal : Gate (Qubits (m + n))
  /-- Output gate whose projected block is certified by the endpoint. -/
  output : Gate (Qubits (a + n))
  /-- Typed output circuit carrying the trusted resource profile. -/
  circuit : Circuit (Qubits (a + n))
  output_matrix_eq :
    (output : HilbertOperator (Qubits (a + n))) =
      (circuit.matrix : HilbertOperator (Qubits (a + n)))
  /-- Hermitian-QSVT-specific trusted query and gate counters. -/
  resources : HermitianResourceProfile
  circuit_resources :
    ResourceProfile.HasExactCounts circuit.resources
      resources.oracleQueries 0 resources.elementaryGates 0
  sourceBlockEncoding : ExactBlockEncoding m n signal A
  /-- Transformation ancillas added on top of the source block-encoding ancillas. -/
  extraAncillaQubits : Nat
  /-- Total block ancillas exposed by the output block encoding. -/
  totalBlockAncilla : Nat
  totalBlockAncilla_eq : totalBlockAncilla = m + extraAncillaQubits

namespace HermitianQSVTWord

/-- The word uses the registered source block encoding as its signal oracle. -/
def UsesSignal {m a n : Nat} {A : HilbertOperator (Qubits n)} (word : HermitianQSVTWord m a n A)
    (U : Gate (Qubits (m + n))) : Prop :=
  word.signal = U

/-- The output gate is the mathematical matrix of the typed circuit stored in
the Hermitian QSVT word. -/
theorem output_eq_circuit_matrix {m a n : Nat} {A : HilbertOperator (Qubits n)}
    (word : HermitianQSVTWord m a n A) :
    (word.output : HilbertOperator (Qubits (a + n))) =
      (word.circuit.matrix : HilbertOperator (Qubits (a + n))) :=
  word.output_matrix_eq

end HermitianQSVTWord

/-- Circuit-level wrapper for the Hadamard phase ancilla and reassociation used
by Hermitian real-parity endpoints. The history keeps the projected-QSVT circuit
as a subhistory, instead of replacing it by an unrelated opaque output gate. -/
noncomputable def phaseHadamardReassociateCircuit {m n : Nat}
    (body : Circuit (Qubits (1 + (m + n)))) (profile : HermitianResourceProfile) :
    Circuit (Qubits ((1 + m) + n)) where
  history := CircuitHistory.seq body.history
    (CircuitHistory.atom "qsvt-phase-hadamard-reassociate")
  matrix := reassociatePhaseAncillaGate (m := m) (n := n)
    (phaseHadamardWrapper body.matrix)
  resources := profile.toCircuitResourceProfile
  depth := body.depth + 1
  queryDepth := body.queryDepth

@[simp]
theorem phaseHadamardReassociateCircuit_matrix {m n : Nat}
    (body : Circuit (Qubits (1 + (m + n)))) (profile : HermitianResourceProfile) :
    ((phaseHadamardReassociateCircuit (m := m) (n := n) body profile).matrix :
      HilbertOperator (Qubits ((1 + m) + n))) =
      (reassociatePhaseAncillaGate (m := m) (n := n)
        (phaseHadamardWrapper body.matrix) :
        HilbertOperator (Qubits ((1 + m) + n))) := rfl

theorem phaseHadamardReassociateCircuit_resources_exact {m n : Nat}
    (body : Circuit (Qubits (1 + (m + n)))) (profile : HermitianResourceProfile) :
    ResourceProfile.HasExactCounts
      (phaseHadamardReassociateCircuit (m := m) (n := n) body profile).resources
      profile.oracleQueries 0 profile.elementaryGates 0 := by
  simpa [phaseHadamardReassociateCircuit] using
    HermitianResourceProfile.toCircuitResourceProfile_exact profile

/-- Circuit-level selector average of two branch circuits. -/
noncomputable def averageProjectedBlockCircuit {a n : Nat}
    (left right : Circuit (Qubits (a + n))) (profile : HermitianResourceProfile) :
    Circuit (Qubits ((1 + a) + n)) where
  history := CircuitHistory.seq
    (CircuitHistory.seq left.history right.history)
    (CircuitHistory.atom "qsvt-selector-average")
  matrix := averageProjectedBlockGate (a := a) (n := n) left.matrix right.matrix
  resources := profile.toCircuitResourceProfile
  depth := max left.depth right.depth + 1
  queryDepth := max left.queryDepth right.queryDepth

@[simp]
theorem averageProjectedBlockCircuit_matrix {a n : Nat}
    (left right : Circuit (Qubits (a + n))) (profile : HermitianResourceProfile) :
    ((averageProjectedBlockCircuit (a := a) (n := n) left right profile).matrix :
      HilbertOperator (Qubits ((1 + a) + n))) =
      (averageProjectedBlockGate (a := a) (n := n) left.matrix right.matrix :
        HilbertOperator (Qubits ((1 + a) + n))) := rfl

theorem averageProjectedBlockCircuit_resources_exact {a n : Nat}
    (left right : Circuit (Qubits (a + n))) (profile : HermitianResourceProfile) :
    ResourceProfile.HasExactCounts
      (averageProjectedBlockCircuit (a := a) (n := n) left right profile).resources
      profile.oracleQueries 0 profile.elementaryGates 0 := by
  simpa [averageProjectedBlockCircuit] using
    HermitianResourceProfile.toCircuitResourceProfile_exact profile

/-- Circuit-level global phase applied to one branch. -/
noncomputable def phaseScaledCircuit {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) (body : Circuit R) :
    Circuit R where
  history := CircuitHistory.seq body.history (CircuitHistory.atom "qsvt-branch-phase")
  matrix := phaseScaledGate ζ hζ body.matrix
  resources := body.resources
  depth := body.depth + 1
  queryDepth := body.queryDepth

@[simp]
theorem phaseScaledCircuit_matrix {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) (body : Circuit R) :
    ((phaseScaledCircuit ζ hζ body).matrix : HilbertOperator R) =
      (phaseScaledGate ζ hζ body.matrix : HilbertOperator R) := rfl

/-- Circuit-level carrier for the source alternating phase sequence `U_Φ`. -/
noncomputable def sourceAlternatingPhaseCircuit {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    Circuit (Qubits N) where
  history := CircuitHistory.atom "qsvt-source-alternating-phase"
  matrix := sourceAlternatingPhaseModulation U left right phases
  resources := { ResourceProfile.zero with
    oracleQueries := phases.length
    elementaryGates := phases.length }
  depth := phases.length
  queryDepth := phases.length

@[simp]
theorem sourceAlternatingPhaseCircuit_matrix {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ((sourceAlternatingPhaseCircuit U left right phases).matrix :
      HilbertOperator (Qubits N)) =
      (sourceAlternatingPhaseModulation U left right phases :
        HilbertOperator (Qubits N)) := rfl

/-- Circuit-level selector average of four branch circuits. -/
noncomputable def fourWayAverageProjectedBlockCircuit {a n : Nat}
    (c00 c01 c10 c11 : Circuit (Qubits (a + n)))
    (profile : HermitianResourceProfile) :
    Circuit (Qubits ((1 + (1 + a)) + n)) where
  history := CircuitHistory.seq
    (CircuitHistory.seq
      (CircuitHistory.seq c00.history c01.history)
      (CircuitHistory.seq c10.history c11.history))
    (CircuitHistory.atom "qsvt-four-way-selector-average")
  matrix := fourWayAverageProjectedBlockGate (a := a) (n := n)
    c00.matrix c01.matrix c10.matrix c11.matrix
  resources := profile.toCircuitResourceProfile
  depth := max (max c00.depth c01.depth) (max c10.depth c11.depth) + 1
  queryDepth := max (max c00.queryDepth c01.queryDepth) (max c10.queryDepth c11.queryDepth)

@[simp]
theorem fourWayAverageProjectedBlockCircuit_matrix {a n : Nat}
    (c00 c01 c10 c11 : Circuit (Qubits (a + n)))
    (profile : HermitianResourceProfile) :
    ((fourWayAverageProjectedBlockCircuit (a := a) (n := n)
      c00 c01 c10 c11 profile).matrix :
      HilbertOperator (Qubits ((1 + (1 + a)) + n))) =
      (fourWayAverageProjectedBlockGate (a := a) (n := n)
        c00.matrix c01.matrix c10.matrix c11.matrix :
        HilbertOperator (Qubits ((1 + (1 + a)) + n))) := rfl

theorem fourWayAverageProjectedBlockCircuit_resources_exact {a n : Nat}
    (c00 c01 c10 c11 : Circuit (Qubits (a + n)))
    (profile : HermitianResourceProfile) :
    ResourceProfile.HasExactCounts
      (fourWayAverageProjectedBlockCircuit (a := a) (n := n)
        c00 c01 c10 c11 profile).resources
      profile.oracleQueries 0 profile.elementaryGates 0 := by
  simpa [fourWayAverageProjectedBlockCircuit] using
    HermitianResourceProfile.toCircuitResourceProfile_exact profile

/-- The zero-ancilla projected source block has the same top-left block as the
underlying source gate.  This is the bookkeeping bridge from the source
projected statement to ordinary block-encoding notation. -/
theorem projectedBlock_sourceProjectedBlock_zeroAncilla {m n : Nat}
    (V : Gate (Qubits (m + n))) :
    projectedBlock m n
        (sourceProjectedBlock (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) V) =
      projectedBlock m n (V : HilbertOperator (Qubits (m + n))) := by
  unfold sourceProjectedBlock
  rw [← zeroAncillaEmbeddedOperator_one (a := m) (n := n)]
  rw [projectedBlock_mul_zeroAncillaEmbeddedOperator_right]
  rw [projectedBlock_zeroAncillaEmbeddedOperator_mul_left]
  simp

/-- Source-level projected QSVT, specialized to an exact Hermitian block
encoding, yields an exact block encoding of the corresponding polynomial.

This is the endpoint form used by shared-control QSVT combinations: the branch
gate is the source alternating phase sequence itself, rather than an already
Hadamard-wrapped public-real branch [GSLW19, BlockHam.tex:768-887,1936-1952]. -/
theorem exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
    {m n d : Nat} {U : Gate (Qubits (m + n))}
    {A : HilbertOperator (Qubits n)} {P : Polynomial ℂ}
    {phases : List ℝ}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hparity : HasParity P d)
    (hblock :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d P phases) :
    ExactBlockEncoding m n
      (sourceAlternatingPhaseModulation U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) phases)
      (polynomialOperator P A) := by
  let zero := OrthogonalProjector.zeroAncilla m n
  constructor
  intro i j
  have hout : projectedOutputProjector zero zero d = zero := by
    simp [projectedOutputProjector]
  have hprojected := congrArg (projectedBlock m n) hblock
  have hsource :
      projectedBlock m n
          (sourceAlternatingPhaseModulation U zero zero phases :
            HilbertOperator (Qubits (m + n))) =
        projectedBlock m n
          (singularValuePolynomial zero d P (projectedUnitaryBlock zero zero U)) := by
    rw [← projectedBlock_sourceProjectedBlock_zeroAncilla
      (m := m) (n := n)
      (sourceAlternatingPhaseModulation U zero zero phases)]
    simpa [zero, hout] using hprojected
  have henc :=
    (exactBlockEncoding_to_projectedUnitaryEncoding hbe).block_eq
  have htarget :
      projectedBlock m n
          (singularValuePolynomial zero d P (projectedUnitaryBlock zero zero U)) =
        polynomialOperator P A := by
    rw [henc]
    exact
      projectedBlock_singularValuePolynomial_zeroAncillaEmbeddedOperator_of_hermitian
        (a := m) (n := n) (L := d) P A hA hparity
  have htop :
      projectedBlock m n
          (sourceAlternatingPhaseModulation U zero zero phases :
            HilbertOperator (Qubits (m + n))) =
        polynomialOperator P A := by
    rw [hsource, htarget]
  exact congrFun (congrFun htop i) j

/-- Four source-level projected-QSVT branches can be averaged with two shared
selector ancillas.  Unlike the fallback `m+3` bookkeeping theorem, each branch
here is the source alternating phase sequence itself, so the output has exactly
`m+2` block-encoding ancillas [GSLW19, BlockHam.tex:886-887,1936-1952]. -/
theorem exactBlockEncoding_fourWaySourceAlternatingPhaseModulation
    {m n d00 d01 d10 d11 : Nat} {U : Gate (Qubits (m + n))}
    {A : HilbertOperator (Qubits n)}
    {P00 P01 P10 P11 : Polynomial ℂ}
    {phases00 phases01 phases10 phases11 : List ℝ}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hparity00 : HasParity P00 d00)
    (hparity01 : HasParity P01 d01)
    (hparity10 : HasParity P10 d10)
    (hparity11 : HasParity P11 d11)
    (hblock00 :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d00 P00 phases00)
    (hblock01 :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d01 P01 phases01)
    (hblock10 :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d10 P10 phases10)
    (hblock11 :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) d11 P11 phases11) :
    ExactBlockEncoding (1 + (1 + m)) n
      (fourWayAverageProjectedBlockGate (a := m) (n := n)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases00)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases01)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases10)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases11))
      ((1 / 4 : ℂ) • polynomialOperator P00 A +
        (1 / 4 : ℂ) • polynomialOperator P01 A +
      ((1 / 4 : ℂ) • polynomialOperator P10 A +
        (1 / 4 : ℂ) • polynomialOperator P11 A)) := by
  have h00 :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases00)
        (polynomialOperator P00 A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparity00 hblock00
  have h01 :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases01)
        (polynomialOperator P01 A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparity01 hblock01
  have h10 :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases10)
        (polynomialOperator P10 A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparity10 hblock10
  have h11 :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phases11)
        (polynomialOperator P11 A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparity11 hblock11
  exact exactBlockEncoding_fourWayAverageProjectedBlockGate
    (a := m) (n := n) h00 h01 h10 h11

/-- Four source-level real/imaginary and even/odd phase branches give the
normalization-four complex Hermitian block-encoding shape with two shared
selector ancillas.  This is the conditional source-circuit form of the complex
note after `thm:arbParity`: the branches are source alternating phase sequences,
not already wrapped real-QSVT outputs [GSLW19, BlockHam.tex:1936-1952]. -/
theorem exactBlockEncoding_complexFourPartSourceAlternatingPhaseModulation
    {m n dReEven dReOdd dImEven dImOdd : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    {P : Polynomial Complex}
    {phasesReEven phasesReOdd phasesImEven phasesImOdd : List Real}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hparityReEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) dReEven)
    (hparityReOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) dReOdd)
    (hparityImEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P))) dImEven)
    (hparityImOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P))) dImOdd)
    (hblockReEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P)))
        phasesReEven)
    (hblockReOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P)))
        phasesReOdd)
    (hblockImEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P)))
        phasesImEven)
    (hblockImOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P)))
        phasesImOdd) :
    ExactBlockEncoding (1 + (1 + m)) n
      (fourWayAverageProjectedBlockGate (a := m) (n := n)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReEven)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReOdd)
        (phaseScaledGate Complex.I complex_normSq_I
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesImEven))
        (phaseScaledGate Complex.I complex_normSq_I
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesImOdd)))
      ((1 / 4 : Complex) • polynomialOperator P A) := by
  have hReEven :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReEven)
        (polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialRealPart P))) A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparityReEven hblockReEven
  have hReOdd :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReOdd)
        (polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialRealPart P))) A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparityReOdd hblockReOdd
  have hImEven :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesImEven)
        (polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparityImEven hblockImEven
  have hImOdd :
      ExactBlockEncoding m n
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesImOdd)
        (polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A) :=
    exactBlockEncoding_sourceAlternatingPhaseModulation_of_sourceCorrectness
      hbe hA hparityImOdd hblockImOdd
  exact
    exactBlockEncoding_complexFourPartAverageProjectedBlockGate
      (a := m) (n := n) P A hReEven hReOdd hImEven hImOdd

/-- Block-encoding form of
`exactBlockEncoding_complexFourPartSourceAlternatingPhaseModulation`: the same
shared source-level four-way circuit is a `(4,m+2,0)` block encoding of the
complex Hermitian polynomial target. -/
theorem blockEncoding_complexFourPartSourceAlternatingPhaseModulation
    {m n dReEven dReOdd dImEven dImOdd : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    {P : Polynomial Complex}
    {phasesReEven phasesReOdd phasesImEven phasesImOdd : List Real}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hparityReEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) dReEven)
    (hparityReOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) dReOdd)
    (hparityImEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P))) dImEven)
    (hparityImOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P))) dImOdd)
    (hblockReEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P)))
        phasesReEven)
    (hblockReOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P)))
        phasesReOdd)
    (hblockImEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P)))
        phasesImEven)
    (hblockImOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P)))
        phasesImOdd) :
    BlockEncoding 4 (1 + (1 + m)) n 0
      (fourWayAverageProjectedBlockGate (a := m) (n := n)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReEven)
        (sourceAlternatingPhaseModulation U
          (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) phasesReOdd)
        (phaseScaledGate Complex.I complex_normSq_I
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesImEven))
        (phaseScaledGate Complex.I complex_normSq_I
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesImOdd)))
      (polynomialOperator P A) := by
  have hExact :=
    exactBlockEncoding_complexFourPartSourceAlternatingPhaseModulation
      (m := m) (n := n) (U := U) (A := A) (P := P)
      hbe hA hparityReEven hparityReOdd hparityImEven hparityImOdd
      hblockReEven hblockReOdd hblockImEven hblockImOdd
  have hScaled :
      ExactBlockEncoding (1 + (1 + m)) n
        (fourWayAverageProjectedBlockGate (a := m) (n := n)
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesReEven)
          (sourceAlternatingPhaseModulation U
            (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) phasesReOdd)
          (phaseScaledGate Complex.I complex_normSq_I
            (sourceAlternatingPhaseModulation U
              (OrthogonalProjector.zeroAncilla m n)
              (OrthogonalProjector.zeroAncilla m n) phasesImEven))
          (phaseScaledGate Complex.I complex_normSq_I
            (sourceAlternatingPhaseModulation U
              (OrthogonalProjector.zeroAncilla m n)
              (OrthogonalProjector.zeroAncilla m n) phasesImOdd)))
        (((4 : Real)⁻¹ : Complex) • polynomialOperator P A) := by
    simpa [one_div] using hExact
  exact ExactBlockEncoding.toScaledBlockEncoding (alpha := 4) (by norm_num) hScaled

namespace Signal.HermitianRealParity

/-- The real matching-parity Hermitian QSVT endpoint.  The polynomial-side
hypotheses record the degree, parity, and spectral contraction choices of the
source theorem; the conclusion gives a concrete output gate whose projected
block is exactly `P(A)` together with the exact resource counters. -/
theorem sourceMain {m n L : Nat} {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (hLpos : 0 < L) :
    ∃ word : HermitianQSVTWord m (1 + m) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + m) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 1 ∧
        word.resources = realParityResources m L ∧
        (realPolynomialToComplex PRe).natDegree ≤ L ∧
        HasParity (realPolynomialToComplex PRe) L ∧
        HermitianResourceProfile.HasExactCounts word.resources L 0 1 ((m + 1) * L) ∧
        NatBigO (fun d : ℕ => (realParityResources m d).oracleQueries) (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ => (realParityResources m d).elementaryGates)
          (fun d : ℕ => (m + 1) * d) := by
  let zero := OrthogonalProjector.zeroAncilla m n
  let projected :=
    realProjectedQSVTOfMatchingParity (U := U) zero zero hP hLpos
  let circuit :=
    phaseHadamardReassociateCircuit (m := m) (n := n) projected.circuit
      (realParityResources m L)
  let output :=
    circuit.matrix
  have houtput :
      ExactBlockEncoding (1 + m) n output
        (polynomialOperator (realPolynomialToComplex PRe) A) := by
    constructor
    intro i j
    have hout : projectedOutputProjector zero zero L = zero := by
      simp [projectedOutputProjector]
    have hprojected :=
      congrArg (projectedBlock m n) projected.block_eq
    have hprojected' :
        projectedBlock m n
            (projectedPhasePlusBlock zero zero projected.circuit.matrix) =
          projectedBlock m n
            (singularValuePolynomial zero L (realPolynomialToComplex PRe)
              (projectedUnitaryBlock zero zero U)) := by
      simpa [hout, zero] using hprojected
    have henc :=
      (exactBlockEncoding_to_projectedUnitaryEncoding hbe).block_eq
    have htarget :
        projectedBlock m n
            (singularValuePolynomial zero L (realPolynomialToComplex PRe)
              (projectedUnitaryBlock zero zero U)) =
          polynomialOperator (realPolynomialToComplex PRe) A := by
      rw [henc]
      exact
        projectedBlock_singularValuePolynomial_zeroAncillaEmbeddedOperator_of_hermitian
          (a := m) (n := n) (L := L) (realPolynomialToComplex PRe) A hA
          (ReflectionQSPPhaseSynthesis.hasParity_realPolynomialToComplex hP.parity)
    have hblock :
        projectedBlock (1 + m) n
            (output : HilbertOperator (Qubits ((1 + m) + n))) =
          polynomialOperator (realPolynomialToComplex PRe) A := by
      unfold output circuit
      rw [phaseHadamardReassociateCircuit_matrix]
      rw [projectedBlock_reassociatedPhaseHadamardWrapper]
      rw [← projectedBlock_projectedPhasePlusBlock_zeroAncilla projected.circuit.matrix]
      rw [hprojected', htarget]
    exact congrFun (congrFun hblock i) j
  refine ⟨{
      signal := U,
      output := output,
      circuit := circuit,
      output_matrix_eq := rfl,
      resources := realParityResources m L,
      circuit_resources := by
        simpa [circuit] using
          phaseHadamardReassociateCircuit_resources_exact
            (m := m) (n := n) projected.circuit (realParityResources m L),
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 1,
      totalBlockAncilla := 1 + m,
      totalBlockAncilla_eq := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, by simp; omega,
    rfl, by simpa [realPolynomialToComplex_natDegree] using hP.degree_le,
    ReflectionQSPPhaseSynthesis.hasParity_realPolynomialToComplex hP.parity,
    realParityResources_exact m L, realParityOracleQueries_bigO m,
    realParityElementaryGates_bigO m⟩

/-- A real matching-parity branch can always be represented as a block-encoding
with the same carrier shape as the source real-parity QSVT endpoint.  Positive
degree branches use the source circuit; degree-zero branches are represented by
the elementary scalar dilation.  This keeps the arbitrary-parity reductions from
falling back to an unrelated spectral construction. -/
theorem exists_word_of_matchingParity {m n d : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity d PRe) :
    ∃ word : HermitianQSVTWord m (1 + m) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + m) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.resources = realParityResources m d := by
  by_cases hpos : 0 < d
  · rcases sourceMain (m := m) (n := n) (L := d) (U := U) (A := A)
        PRe hbe hA hP hpos with
      ⟨word, huses, henc, -, hresources, -, -, -, -, -⟩
    exact ⟨word, huses, henc, hresources⟩
  · have hd0 : d = 0 := by omega
    have hdegRe : PRe.natDegree = 0 := by
      have hle0 : PRe.natDegree ≤ 0 := by
        simpa [hd0] using hP.degree_le
      exact Nat.eq_zero_of_le_zero hle0
    have hdeg :
        (realPolynomialToComplex PRe).natDegree = 0 := by
      simp [realPolynomialToComplex_natDegree, hdegRe]
    have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> norm_num
    have hcoeffNorm :
        ‖(realPolynomialToComplex PRe).coeff 0‖ ≤ 1 := by
      have hbounded := hP.bounded 0 hzero
      have hcoeffAbs : |PRe.coeff 0| ≤ 1 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hbounded
      simpa [realPolynomialToComplex, Polynomial.coeff_map] using hcoeffAbs
    have hcoeffSq :
        ‖(realPolynomialToComplex PRe).coeff 0‖ ^ 2 ≤ (1 : ℝ) := by
      nlinarith [hcoeffNorm, norm_nonneg ((realPolynomialToComplex PRe).coeff 0)]
    have hcontract :
        Complex.normSq ((realPolynomialToComplex PRe).coeff 0) ≤ 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hcoeffSq
    let output :=
      scalarDilationWithSourceAncillas (m := m) (n := n)
        ((realPolynomialToComplex PRe).coeff 0) hcontract
    let circuit :=
      Circuit.ofGate "qsvt-scalar-dilation" output
        (realParityResources m d).toCircuitResourceProfile 0 0
    have henc :
        ExactBlockEncoding (1 + m) n output
          (polynomialOperator (realPolynomialToComplex PRe) A) :=
      exactBlockEncoding_constantPolynomialWithSourceAncillas
        (m := m) (n := n) (P := realPolynomialToComplex PRe) A hdeg hcontract
    refine ⟨{
        signal := U,
        output := output,
        circuit := circuit,
        output_matrix_eq := by
          simp [circuit, Circuit.ofGate],
        resources := realParityResources m d,
        circuit_resources := by
          simpa [circuit] using
            HermitianResourceProfile.toCircuitResourceProfile_exact
              (realParityResources m d),
        sourceBlockEncoding := hbe,
        extraAncillaQubits := 1,
        totalBlockAncilla := 1 + m,
        totalBlockAncilla_eq := by omega
      }, rfl, henc, rfl⟩

/-- Gate-only projection of `exists_word_of_matchingParity` for older internal
block-encoding helpers. -/
theorem exists_output_of_matchingParity {m n d : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity d PRe) :
    ∃ V : Gate (Qubits ((1 + m) + n)),
      ExactBlockEncoding (1 + m) n V
        (polynomialOperator (realPolynomialToComplex PRe) A) := by
  rcases exists_word_of_matchingParity (m := m) (n := n) (d := d)
      (U := U) (A := A) PRe hbe hA hP with
    ⟨word, -, henc, -⟩
  exact ⟨word.output, henc⟩

end Signal.HermitianRealParity

namespace Signal.HermitianRealArbitrary

/-- Real arbitrary-parity Hermitian QSVT for the main positive-branch case.
The proof follows `thm:arbParity`: implement the doubled even and odd branches
with the matching-parity corollary, then take one selector average
[GSLW19, BlockHam.tex:1936-1951].  The low-degree edge cases are handled
separately before this internal theorem is exposed as a public endpoint. -/
theorem main_of_positive_branch_degrees {m n L : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : PRe.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |PRe.eval x| ≤ (1 / 2 : ℝ))
    (hEvenPos : 0 < ReflectionQSPPhaseSynthesis.evenBranchDegree L)
    (hOddPos : 0 < ReflectionQSPPhaseSynthesis.oddBranchDegree L) :
    ∃ word : HermitianQSVTWord m (1 + (1 + m)) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + (1 + m)) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 2 ∧
        word.resources = hermitianComplexResources m L ∧
        NatBigO (fun d : ℕ => (hermitianComplexResources m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ => (hermitianComplexResources m d).elementaryGates)
          (fun d : ℕ => (m + 1) * d) := by
  let Peven : Polynomial ℝ := (2 : ℝ) • realPolynomialEvenPart PRe
  let Podd : Polynomial ℝ := (2 : ℝ) • realPolynomialOddPart PRe
  have hLpos : 0 < L := by
    by_contra hnot
    have hLzero : L = 0 := Nat.eq_zero_of_not_pos hnot
    simp [ReflectionQSPPhaseSynthesis.oddBranchDegree, hLzero] at hOddPos
  have hPeven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) Peven := by
    simpa [Peven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_twoEvenPart_branch_of_boundedByHalf
          (L := L) PRe hdegree hbound
  have hPodd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) Podd := by
    simpa [Podd] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_twoOddPart_branch_of_boundedByHalf
          (L := L) PRe hdegree hLpos hbound
  rcases QSVT.Signal.HermitianRealParity.sourceMain (m := m) (n := n)
      (L := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) Peven hbe hA hPeven hEvenPos with
    ⟨evenWord, hevenUses, hEvenEnc, -, -, -, -, -, -⟩
  rcases QSVT.Signal.HermitianRealParity.sourceMain (m := m) (n := n)
      (L := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) Podd hbe hA hPodd hOddPos with
    ⟨oddWord, hoddUses, hOddEnc, -, -, -, -, -, -⟩
  have hevenSignal : evenWord.signal = U := hevenUses
  have hoddSignal : oddWord.signal = U := hoddUses
  have hEvenEncCircuit :
      ExactBlockEncoding (1 + m) n evenWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex Peven) A) := by
    constructor
    intro i j
    simpa [← evenWord.output_matrix_eq] using hEvenEnc.block_eq i j
  have hOddEncCircuit :
      ExactBlockEncoding (1 + m) n oddWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex Podd) A) := by
    constructor
    intro i j
    simpa [← oddWord.output_matrix_eq] using hOddEnc.block_eq i j
  let circuit :=
    averageProjectedBlockCircuit (a := 1 + m) (n := n)
      evenWord.circuit oddWord.circuit (hermitianComplexResources m L)
  let output :=
    circuit.matrix
  have houtput :
      ExactBlockEncoding (1 + (1 + m)) n output
        (polynomialOperator (realPolynomialToComplex PRe) A) := by
    unfold output circuit
    simpa [averageProjectedBlockCircuit, Peven, Podd] using
      exactBlockEncoding_realEvenOddDoubleAverageProjectedBlockGate
        (a := 1 + m) (n := n) PRe A hEvenEncCircuit hOddEncCircuit
  refine ⟨{
      signal := U,
      output := output,
      circuit := circuit,
      output_matrix_eq := rfl,
      resources := hermitianComplexResources m L,
      circuit_resources := by
        simpa [circuit] using
          averageProjectedBlockCircuit_resources_exact
            (a := 1 + m) (n := n) evenWord.circuit oddWord.circuit
            (hermitianComplexResources m L),
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 2,
      totalBlockAncilla := m + 2,
      totalBlockAncilla_eq := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, rfl, rfl,
    hermitianComplexOracleQueries_bigO m,
    hermitianComplexElementaryGates_bigO m⟩

/-- Real arbitrary-parity Hermitian QSVT.  This removes the positive-branch
side conditions from `main_of_positive_branch_degrees` by using constant-safe
branch realizations for zero-degree even/odd pieces, while preserving the same
source-circuit selector-average shape from `thm:arbParity`
[GSLW19, BlockHam.tex:1936-1951]. -/
theorem sourceMain {m n L : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (PRe : Polynomial ℝ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : PRe.natDegree ≤ L)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |PRe.eval x| ≤ (1 / 2 : ℝ)) :
    ∃ word : HermitianQSVTWord m (1 + (1 + m)) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + (1 + m)) n word.output
          (polynomialOperator (realPolynomialToComplex PRe) A) ∧
        word.totalBlockAncilla = m + 2 ∧
        word.resources = hermitianComplexResources m L ∧
        NatBigO (fun d : ℕ => (hermitianComplexResources m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ => (hermitianComplexResources m d).elementaryGates)
          (fun d : ℕ => (m + 1) * d) := by
  let Peven : Polynomial ℝ := (2 : ℝ) • realPolynomialEvenPart PRe
  let Podd : Polynomial ℝ := (2 : ℝ) • realPolynomialOddPart PRe
  have hPeven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) Peven := by
    simpa [Peven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_twoEvenPart_branch_of_boundedByHalf
          (L := L) PRe hdegree hbound
  have hPodd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) Podd := by
    simpa [Podd] using
      realBoundedMatchingParity_twoOddPart_branch_of_boundedByHalf_including_constant
          (L := L) PRe hdegree hbound
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) Peven hbe hA hPeven with
    ⟨evenWord, -, hEvenEnc, -⟩
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) Podd hbe hA hPodd with
    ⟨oddWord, -, hOddEnc, -⟩
  have hEvenEncCircuit :
      ExactBlockEncoding (1 + m) n evenWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex Peven) A) := by
    constructor
    intro i j
    simpa [← evenWord.output_matrix_eq] using hEvenEnc.block_eq i j
  have hOddEncCircuit :
      ExactBlockEncoding (1 + m) n oddWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex Podd) A) := by
    constructor
    intro i j
    simpa [← oddWord.output_matrix_eq] using hOddEnc.block_eq i j
  let circuit :=
    averageProjectedBlockCircuit (a := 1 + m) (n := n)
      evenWord.circuit oddWord.circuit (hermitianComplexResources m L)
  let output :=
    circuit.matrix
  have houtput :
      ExactBlockEncoding (1 + (1 + m)) n output
        (polynomialOperator (realPolynomialToComplex PRe) A) := by
    unfold output circuit
    simpa [averageProjectedBlockCircuit, Peven, Podd] using
      exactBlockEncoding_realEvenOddDoubleAverageProjectedBlockGate
        (a := 1 + m) (n := n) PRe A hEvenEncCircuit hOddEncCircuit
  refine ⟨{
      signal := U,
      output := output,
      circuit := circuit,
      output_matrix_eq := rfl,
      resources := hermitianComplexResources m L,
      circuit_resources := by
        simpa [circuit] using
          averageProjectedBlockCircuit_resources_exact
            (a := 1 + m) (n := n) evenWord.circuit oddWord.circuit
            (hermitianComplexResources m L),
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 2,
      totalBlockAncilla := m + 2,
      totalBlockAncilla_eq := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, rfl, rfl,
    hermitianComplexOracleQueries_bigO m,
    hermitianComplexElementaryGates_bigO m⟩

end Signal.HermitianRealArbitrary

namespace Signal.HermitianComplex

/-- Conditional complex Hermitian endpoint from four direct source-level branches.

If the four real/imaginary even/odd terms are already implemented as direct
source alternating phase sequences, the two shared selector ancillas give a
sharper `(4,m+2,0)` support shape.  These branch hypotheses are stronger than
the real-completion conclusion of `cor:realP`, so the public complex endpoint
below uses the unconditional four-real-branch construction instead
[GSLW19, BlockHam.tex:1936-1952]. -/
theorem ofFourSourceBranches {m n L dReEven dReOdd dImEven dImOdd : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    {P : Polynomial Complex}
    {phasesReEven phasesReOdd phasesImEven phasesImOdd : List Real}
    (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : P.natDegree ≤ L)
    (hparityReEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) dReEven)
    (hparityReOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) dReOdd)
    (hparityImEven :
      HasParity
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P))) dImEven)
    (hparityImOdd :
      HasParity
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P))) dImOdd)
    (hblockReEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P)))
        phasesReEven)
    (hblockReOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dReOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P)))
        phasesReOdd)
    (hblockImEven :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImEven
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P)))
        phasesImEven)
    (hblockImOdd :
      SourceProjectedQSVTBlockCorrectness U
        (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) dImOdd
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P)))
        phasesImOdd) :
    ∃ word : HermitianQSVTWord m (1 + (1 + m)) n A,
      word.UsesSignal U ∧
        BlockEncoding 4 (1 + (1 + m)) n 0 word.output
          (polynomialOperator P A) ∧
        word.totalBlockAncilla = m + 2 ∧
        word.resources = hermitianComplexResources m L ∧
        P.natDegree ≤ L ∧
        HermitianResourceProfile.HasExactCounts word.resources L 1 2 ((m + 1) * L) ∧
        NatBigO (fun d : Nat => (hermitianComplexResources m d).oracleQueries)
          (fun d : Nat => d) ∧
        NatBigO (fun d : Nat => (hermitianComplexResources m d).elementaryGates)
          (fun d : Nat => (m + 1) * d) := by
  let zero := OrthogonalProjector.zeroAncilla m n
  let reEvenCircuit := sourceAlternatingPhaseCircuit U zero zero phasesReEven
  let reOddCircuit := sourceAlternatingPhaseCircuit U zero zero phasesReOdd
  let imEvenCircuit :=
    phaseScaledCircuit Complex.I complex_normSq_I
      (sourceAlternatingPhaseCircuit U zero zero phasesImEven)
  let imOddCircuit :=
    phaseScaledCircuit Complex.I complex_normSq_I
      (sourceAlternatingPhaseCircuit U zero zero phasesImOdd)
  let circuit :=
    fourWayAverageProjectedBlockCircuit (a := m) (n := n)
      reEvenCircuit reOddCircuit imEvenCircuit imOddCircuit
      (hermitianComplexResources m L)
  let output := circuit.matrix
  have houtput :
      BlockEncoding 4 (1 + (1 + m)) n 0 output
        (polynomialOperator P A) := by
    unfold output circuit reEvenCircuit reOddCircuit imEvenCircuit imOddCircuit zero
    simpa [fourWayAverageProjectedBlockCircuit, sourceAlternatingPhaseCircuit,
      phaseScaledCircuit] using
      blockEncoding_complexFourPartSourceAlternatingPhaseModulation
        (m := m) (n := n) (U := U) (A := A) (P := P)
        hbe hA hparityReEven hparityReOdd hparityImEven hparityImOdd
        hblockReEven hblockReOdd hblockImEven hblockImOdd
  refine ⟨{
      signal := U,
      output := output,
      circuit := circuit,
      output_matrix_eq := rfl,
      resources := hermitianComplexResources m L,
      circuit_resources := by
        simpa [circuit] using
          fourWayAverageProjectedBlockCircuit_resources_exact
            (a := m) (n := n) reEvenCircuit reOddCircuit imEvenCircuit imOddCircuit
            (hermitianComplexResources m L),
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 2,
      totalBlockAncilla := m + 2,
      totalBlockAncilla_eq := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, rfl, rfl, hdegree,
    hermitianComplexResources_exact m L,
    hermitianComplexOracleQueries_bigO m,
    hermitianComplexElementaryGates_bigO m⟩

/-- Combine complex even/odd branch encodings into the Hermitian complex QSVT
endpoint shape with two total transformation ancillas.  This is the
source-circuit interface left after the complex note following `thm:arbParity`:
once the two matching-parity complex branches are implemented by QSVT circuits,
one selector average reconstructs `P(A)` [GSLW19, BlockHam.tex:1952]. -/
theorem ofComplexEvenOddBranchEncodings {m n L : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (P : Polynomial ℂ) (hbe : ExactBlockEncoding m n U A)
    {VEven VOdd : Gate (Qubits ((1 + m) + n))}
    (hEven : ExactBlockEncoding (1 + m) n VEven
      (polynomialOperator ((2 : ℂ) • complexPolynomialEvenPart P) A))
    (hOdd : ExactBlockEncoding (1 + m) n VOdd
      (polynomialOperator ((2 : ℂ) • complexPolynomialOddPart P) A))
    (hdegree : P.natDegree ≤ L) :
    ∃ word : HermitianQSVTWord m (1 + (1 + m)) n A,
      word.UsesSignal U ∧
        ExactBlockEncoding (1 + (1 + m)) n word.output
          (polynomialOperator P A) ∧
        word.totalBlockAncilla = m + 2 ∧
        word.resources = hermitianComplexResources m L ∧
        P.natDegree ≤ L ∧
        NatBigO (fun d : ℕ => (hermitianComplexResources m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ => (hermitianComplexResources m d).elementaryGates)
          (fun d : ℕ => (m + 1) * d) := by
  let evenCircuit :=
    Circuit.ofGate "qsvt-complex-even-branch" VEven
      (hermitianComplexResources m L).toCircuitResourceProfile 0 0
  let oddCircuit :=
    Circuit.ofGate "qsvt-complex-odd-branch" VOdd
      (hermitianComplexResources m L).toCircuitResourceProfile 0 0
  let circuit :=
    averageProjectedBlockCircuit (a := 1 + m) (n := n)
      evenCircuit oddCircuit (hermitianComplexResources m L)
  let output := circuit.matrix
  have houtput :
      ExactBlockEncoding (1 + (1 + m)) n output
        (polynomialOperator P A) := by
    unfold output circuit evenCircuit oddCircuit
    change ExactBlockEncoding (1 + (1 + m)) n
      (averageProjectedBlockGate (a := 1 + m) (n := n) VEven VOdd)
      (polynomialOperator P A)
    exact exactBlockEncoding_complexEvenOddDoubleAverageProjectedBlockGate
      (a := 1 + m) (n := n) P A hEven hOdd
  refine ⟨{
      signal := U,
      output := output,
      circuit := circuit,
      output_matrix_eq := rfl,
      resources := hermitianComplexResources m L,
      circuit_resources := by
        simpa [circuit] using
          averageProjectedBlockCircuit_resources_exact
            (a := 1 + m) (n := n) evenCircuit oddCircuit
            (hermitianComplexResources m L),
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 2,
      totalBlockAncilla := m + 2,
      totalBlockAncilla_eq := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, rfl, rfl, hdegree,
    hermitianComplexOracleQueries_bigO m,
    hermitianComplexElementaryGates_bigO m⟩

/-- Naive four-real-branch complex Hermitian QSVT block encoding.

This theorem verifies the source note after `thm:arbParity`: real/imaginary and
even/odd branches combine to a normalization-four encoding of `P(A)`.  The
current public complex endpoint uses this source-supported construction, with
three transformation ancillas (`m+3`) and constant controlled-query overhead
[GSLW19, BlockHam.tex:1936-1952]. -/
theorem naiveFourRealBranchBlockEncoding {m n L : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (P : Polynomial ℂ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : P.natDegree ≤ L)
    (hbound :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ output : Gate (Qubits ((1 + (1 + (1 + m))) + n)),
      BlockEncoding 4 (1 + (1 + (1 + m))) n 0 output
        (polynomialOperator P A) := by
  let PReEven : Polynomial ℝ :=
    realPolynomialEvenPart (complexPolynomialRealPart P)
  let PReOdd : Polynomial ℝ :=
    realPolynomialOddPart (complexPolynomialRealPart P)
  let PImEven : Polynomial ℝ :=
    realPolynomialEvenPart (complexPolynomialImagPart P)
  let PImOdd : Polynomial ℝ :=
    realPolynomialOddPart (complexPolynomialImagPart P)
  have hReEven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) PReEven := by
    simpa [PReEven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_realEvenPart_branch_of_normSq_le
        (L := L) P hdegree hbound
  have hReOdd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) PReOdd := by
    simpa [PReOdd] using
      realBoundedMatchingParity_realOddPart_branch_of_normSq_le_including_constant
        (L := L) P hdegree hbound
  have hImEven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) PImEven := by
    simpa [PImEven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_imagEvenPart_branch_of_normSq_le
        (L := L) P hdegree hbound
  have hImOdd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) PImOdd := by
    simpa [PImOdd] using
      realBoundedMatchingParity_imagOddPart_branch_of_normSq_le_including_constant
        (L := L) P hdegree hbound
  rcases QSVT.Signal.HermitianRealParity.exists_output_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) PReEven hbe hA hReEven with
    ⟨VReEven, hVReEven⟩
  rcases QSVT.Signal.HermitianRealParity.exists_output_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) PReOdd hbe hA hReOdd with
    ⟨VReOdd, hVReOdd⟩
  rcases QSVT.Signal.HermitianRealParity.exists_output_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) PImEven hbe hA hImEven with
    ⟨VImEven, hVImEven⟩
  rcases QSVT.Signal.HermitianRealParity.exists_output_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) PImOdd hbe hA hImOdd with
    ⟨VImOdd, hVImOdd⟩
  let output :=
    fourWayAverageProjectedBlockGate (a := 1 + m) (n := n)
      VReEven VReOdd
      (phaseScaledGate Complex.I complex_normSq_I VImEven)
      (phaseScaledGate Complex.I complex_normSq_I VImOdd)
  have hExact :
      ExactBlockEncoding (1 + (1 + (1 + m))) n output
        ((1 / 4 : ℂ) • polynomialOperator P A) := by
    unfold output
    exact
      exactBlockEncoding_complexFourPartAverageProjectedBlockGate
        (a := 1 + m) (n := n) P A
        hVReEven hVReOdd hVImEven hVImOdd
  refine ⟨output, ?_⟩
  have hExactScaled :
      ExactBlockEncoding (1 + (1 + (1 + m))) n output
        (((4 : ℝ)⁻¹ : ℂ) • polynomialOperator P A) := by
    simpa [one_div] using hExact
  exact ExactBlockEncoding.toScaledBlockEncoding (alpha := 4) (by norm_num) hExactScaled

/-- Complex Hermitian QSVT endpoint through the source-supported four-real-branch
construction.

The complex polynomial is split into real/imaginary and even/odd real branches.
Each branch is synthesized by the real matching-parity projected QSVT route, and
the four branch block encodings are recombined with selector block encodings.
This proves the normalization-four complex Hermitian public endpoint with three
transformation ancillas and the same-circuit resource profile recorded in the
returned word [GSLW19, BlockHam.tex:1936-1952]. -/
theorem sourceMain {m n L : Nat}
    {U : Gate (Qubits (m + n))} {A : HilbertOperator (Qubits n)}
    (P : Polynomial ℂ) (hbe : ExactBlockEncoding m n U A) (hA : A.IsHermitian)
    (hdegree : P.natDegree ≤ L)
    (hbound :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ word : HermitianQSVTWord m (1 + (1 + (1 + m))) n A,
      word.UsesSignal U ∧
        BlockEncoding 4 (1 + (1 + (1 + m))) n 0 word.output
          (polynomialOperator P A) ∧
        word.totalBlockAncilla = m + 3 ∧
        word.resources = hermitianComplexFourBranchResources m L ∧
        P.natDegree ≤ L ∧
        HermitianResourceProfile.HasExactCounts word.resources
          (4 * L) 4 3 (4 * ((m + 1) * L)) ∧
        NatBigO (fun d : ℕ =>
            (hermitianComplexFourBranchResources m d).oracleQueries)
          (fun d : ℕ => d) ∧
        NatBigO (fun d : ℕ =>
            (hermitianComplexFourBranchResources m d).elementaryGates)
          (fun d : ℕ => (m + 1) * d) := by
  let PReEven : Polynomial ℝ :=
    realPolynomialEvenPart (complexPolynomialRealPart P)
  let PReOdd : Polynomial ℝ :=
    realPolynomialOddPart (complexPolynomialRealPart P)
  let PImEven : Polynomial ℝ :=
    realPolynomialEvenPart (complexPolynomialImagPart P)
  let PImOdd : Polynomial ℝ :=
    realPolynomialOddPart (complexPolynomialImagPart P)
  have hReEven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) PReEven := by
    simpa [PReEven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_realEvenPart_branch_of_normSq_le
        (L := L) P hdegree hbound
  have hReOdd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) PReOdd := by
    simpa [PReOdd] using
      realBoundedMatchingParity_realOddPart_branch_of_normSq_le_including_constant
        (L := L) P hdegree hbound
  have hImEven :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.evenBranchDegree L) PImEven := by
    simpa [PImEven] using
      ReflectionQSPPhaseSynthesis.realBoundedMatchingParity_imagEvenPart_branch_of_normSq_le
        (L := L) P hdegree hbound
  have hImOdd :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity
        (ReflectionQSPPhaseSynthesis.oddBranchDegree L) PImOdd := by
    simpa [PImOdd] using
      realBoundedMatchingParity_imagOddPart_branch_of_normSq_le_including_constant
        (L := L) P hdegree hbound
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) PReEven hbe hA hReEven with
    ⟨reEvenWord, -, hReEvenEnc, -⟩
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) PReOdd hbe hA hReOdd with
    ⟨reOddWord, -, hReOddEnc, -⟩
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.evenBranchDegree L)
      (U := U) (A := A) PImEven hbe hA hImEven with
    ⟨imEvenWord, -, hImEvenEnc, -⟩
  rcases QSVT.Signal.HermitianRealParity.exists_word_of_matchingParity (m := m) (n := n)
      (d := ReflectionQSPPhaseSynthesis.oddBranchDegree L)
      (U := U) (A := A) PImOdd hbe hA hImOdd with
    ⟨imOddWord, -, hImOddEnc, -⟩
  have hReEvenCircuit :
      ExactBlockEncoding (1 + m) n reEvenWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex PReEven) A) := by
    constructor
    intro i j
    simpa [← reEvenWord.output_matrix_eq] using hReEvenEnc.block_eq i j
  have hReOddCircuit :
      ExactBlockEncoding (1 + m) n reOddWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex PReOdd) A) := by
    constructor
    intro i j
    simpa [← reOddWord.output_matrix_eq] using hReOddEnc.block_eq i j
  have hImEvenCircuit :
      ExactBlockEncoding (1 + m) n imEvenWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex PImEven) A) := by
    constructor
    intro i j
    simpa [← imEvenWord.output_matrix_eq] using hImEvenEnc.block_eq i j
  have hImOddCircuit :
      ExactBlockEncoding (1 + m) n imOddWord.circuit.matrix
        (polynomialOperator (realPolynomialToComplex PImOdd) A) := by
    constructor
    intro i j
    simpa [← imOddWord.output_matrix_eq] using hImOddEnc.block_eq i j
  let imEvenCircuit := phaseScaledCircuit Complex.I complex_normSq_I imEvenWord.circuit
  let imOddCircuit := phaseScaledCircuit Complex.I complex_normSq_I imOddWord.circuit
  let circuit :=
    fourWayAverageProjectedBlockCircuit (a := 1 + m) (n := n)
      reEvenWord.circuit reOddWord.circuit imEvenCircuit imOddCircuit
      (hermitianComplexFourBranchResources m L)
  let output := circuit.matrix
  have hExact :
      ExactBlockEncoding (1 + (1 + (1 + m))) n output
        ((1 / 4 : ℂ) • polynomialOperator P A) := by
    unfold output circuit imEvenCircuit imOddCircuit
    simpa [fourWayAverageProjectedBlockCircuit, phaseScaledCircuit,
      PReEven, PReOdd, PImEven, PImOdd] using
      exactBlockEncoding_complexFourPartAverageProjectedBlockGate
        (a := 1 + m) (n := n) P A
        hReEvenCircuit hReOddCircuit hImEvenCircuit hImOddCircuit
  have houtput :
      BlockEncoding 4 (1 + (1 + (1 + m))) n 0 output
        (polynomialOperator P A) := by
    have hExactScaled :
        ExactBlockEncoding (1 + (1 + (1 + m))) n output
          (((4 : ℝ)⁻¹ : ℂ) • polynomialOperator P A) := by
      simpa [one_div] using hExact
    exact ExactBlockEncoding.toScaledBlockEncoding (alpha := 4) (by norm_num) hExactScaled
  refine ⟨{
      signal := U,
      output := output,
      circuit := circuit,
      output_matrix_eq := rfl,
      resources := hermitianComplexFourBranchResources m L,
      circuit_resources := by
        simpa [circuit] using
          fourWayAverageProjectedBlockCircuit_resources_exact
            (a := 1 + m) (n := n)
            reEvenWord.circuit reOddWord.circuit imEvenCircuit imOddCircuit
            (hermitianComplexFourBranchResources m L),
      sourceBlockEncoding := hbe,
      extraAncillaQubits := 3,
      totalBlockAncilla := m + 3,
      totalBlockAncilla_eq := by omega
    }, ?_⟩
  exact ⟨rfl, houtput, rfl, rfl, hdegree,
    hermitianComplexFourBranchResources_exact m L,
    hermitianComplexFourBranchOracleQueries_bigO m,
    hermitianComplexFourBranchElementaryGates_bigO m⟩

end Signal.HermitianComplex

end QSVT

namespace QSVT.Signal

/-- Namespace-local spelling of Hermitian QSVT resource counters. -/
abbrev HermitianResourceProfile :=
  QuantumAlg.QSP.MultiQubit.QSVT.HermitianResourceProfile

/-- Namespace-local spelling of a Hermitian QSVT word. -/
abbrev HermitianQSVTWord (m a n : Nat) (A : HilbertOperator (Qubits n)) :=
  QuantumAlg.QSP.MultiQubit.QSVT.HermitianQSVTWord m a n A

/-- Namespace-local real-parity Hermitian QSVT resource profile. -/
abbrev realParityResources (m L : ℕ) :=
  QuantumAlg.QSP.MultiQubit.QSVT.realParityResources m L

/-- Namespace-local shared-control complex Hermitian resource profile. -/
abbrev hermitianComplexResources (m L : ℕ) :=
  QuantumAlg.QSP.MultiQubit.QSVT.hermitianComplexResources m L

/-- Namespace-local four-branch complex Hermitian resource profile. -/
abbrev hermitianComplexFourBranchResources (m L : ℕ) :=
  QuantumAlg.QSP.MultiQubit.QSVT.hermitianComplexFourBranchResources m L

end QSVT.Signal

end QSP.MultiQubit

end QuantumAlg
