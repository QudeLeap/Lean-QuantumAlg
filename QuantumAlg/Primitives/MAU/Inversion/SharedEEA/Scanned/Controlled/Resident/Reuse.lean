/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Normal
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Reuse.Ports
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources.Empty

/-!
# The same complete selected inversion on the physically reset Y workspace

The original A payload and Y exchange their static physical roles. The
input, every original small source field, full pool and C/N/W retain
their positions. The backward is the literal adjoint of this placed
forward. Its saved-word parameter uses physical Y order; a caller must
prove the whole boundary state and may not identify that parameter with
the numerical A word without the corresponding reversal.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentReuse

noncomputable section

def layout (width : Nat) : EncodedBit.FullPlacement
    (ControlledResidentFrame.encoding width) (ControlledResidentFrame.encoding width) :=
  (WorkspaceReuse.placement width).appendRight ControlledResidentFrame.flagsEncoding

def forward (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.encoding modulus.size).width).toQuantum :=
  (layout modulus.size).place (ControlledResidentNormal.program modulus nontrivial)

def backward (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledResidentFrame.encoding modulus.size).width).toQuantum :=
  (forward modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

def initial (modulus : Nat) (input savedPhysicalWord : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    ControlledResidentFrame.Data modulus.size :=
  (layout modulus.size).grouping.symm
    (ControlledResident.initial modulus input savedPhysicalWord pool flags)

def result (modulus : Nat) (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (savedPhysicalWord : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    ControlledResidentFrame.Data modulus.size :=
  (layout modulus.size).grouping.symm
    (ControlledResident.result modulus input positive bounded savedPhysicalWord pool flags)

/-- Every original source field and saved physical word belongs to this admitted-input equation. -/
lemma forward_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input savedPhysicalWord : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : ControlledResidentFrame.Flags) (selected : flags.2.1 = true) :
    (forward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode
            (initial modulus input savedPhysicalWord pool flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode
          (result modulus input positive bounded savedPhysicalWord pool flags))) :=
  (layout modulus.size).place_ket_of_eq _ _ _
    (ControlledResidentNormal.program_initial_active modulus nontrivial environment
      input savedPhysicalWord coprime positive bounded pool addressZero prefixZero borrowZero
      flags selected)

/-- The same actual placed forward's own adjoint restores its complete initial boundary. -/
lemma backward_result (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input savedPhysicalWord : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false)
    (flags : ControlledResidentFrame.Flags) (selected : flags.2.1 = true) :
    (backward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledResidentFrame.encoding modulus.size).encode
            (result modulus input positive bounded savedPhysicalWord pool flags)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledResidentFrame.encoding modulus.size).encode
          (initial modulus input savedPhysicalWord pool flags))) := by
  have actual := forward_initial modulus nontrivial environment input savedPhysicalWord
    coprime positive bounded pool addressZero prefixZero borrowZero flags selected
  exact (congrArg (fun state => (backward modulus nontrivial).applyNormalized environment state)
      actual).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
      (forward modulus nontrivial) (backward modulus nontrivial)
      (by
        rw [backward, UnitaryCircuit.dagger_matrix,
          Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
            environment]
        exact Unitary.star_eq_inv _) _)

lemma forward_eventTrace (modulus : Nat) (nontrivial : 1 < modulus) :
    (forward modulus nontrivial).eventTrace =
      (ControlledResidentNormal.program modulus nontrivial).eventTrace :=
  (layout modulus.size).place_eventTrace _

lemma forward_quantumTime (modulus : Nat) (nontrivial : 1 < modulus) :
    (forward modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration =
      (ControlledResidentNormal.program modulus nontrivial).evaluatedEventDepth
        Resource.Event.quantumDuration :=
  (layout modulus.size).place_evaluatedEventDepth _ _

lemma backward_eventCost (modulus : Nat) (nontrivial : 1 < modulus) :
    (backward modulus nontrivial).eventCost = (forward modulus nontrivial).eventCost :=
  AlgorithmGate.algorithmGate_emptyAdjoints_eventCost _

lemma backward_quantumTime (modulus : Nat) (nontrivial : 1 < modulus) :
    (backward modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration =
      (forward modulus nontrivial).evaluatedEventDepth Resource.Event.quantumDuration :=
  AlgorithmGate.algorithmGate_emptyAdjoints_quantumTime _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledResidentReuse
