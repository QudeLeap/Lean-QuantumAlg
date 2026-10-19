/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Exponentiation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Placement
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics

/-!
# Two actual new exponentiations on one shared unit workspace

The unchanged first exponent selects powers of g; the second selects powers
of the inverse target unit. Both actual gate programs address the same power
and zero auxiliary words. Exact realization preserves both exponent fields
and returns the shared auxiliary at every boundary, giving the same source
group action for the short-DLP Born analysis [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Lift the first modular exponentiation across the untouched second exponent
register. -/
def firstExponentiationProgram (m ell width N : Nat)
    (g : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (firstBits (registerParameters m ell width) + ell +
          workspaceBits width)).toQuantum :=
  UnitaryCircuit.insertMiddle
    (leftWidth := firstBits (registerParameters m ell width))
    (middleWidth := ell) (rightWidth := workspaceBits width)
    (exponentiationProgram (ell + m) width N g)

/-- Lift the second modular exponentiation after the first exponent register;
both exponentiations address the same arithmetic workspace. -/
def secondExponentiationProgram (m ell width N : Nat)
    (x : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (firstBits (registerParameters m ell width) + ell +
          workspaceBits width)).toQuantum :=
  castProgram
    (Nat.add_assoc
      (firstBits (registerParameters m ell width)) ell
      (workspaceBits width)).symm
    (UnitaryCircuit.prodRight
      (m := firstBits (registerParameters m ell width))
      (exponentiationProgram ell width N x⁻¹))

/-- Actual shared-workspace program for `(a,b) ↦ g^a * (x^b)⁻¹`. -/
def compiledGroupActionProgram (m ell width N : Nat)
    (g x : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (firstBits (registerParameters m ell width) + ell +
          workspaceBits width)).toQuantum :=
  UnitaryCircuit.seq
    (firstExponentiationProgram m ell width N g)
    (secondExponentiationProgram m ell width N x)

/-- Full-register action of the first lifted exponentiation. -/
def firstExponentiationStep (m ell width N : Nat) (g : (ZMod N)ˣ)
    (input : GroupRegisters m ell width) :
    GroupRegisters m ell width :=
  let updated := exponentiationRawStep
    (firstBits (registerParameters m ell width)) width N g
    (input.1.1, input.2)
  ((updated.1, input.1.2), updated.2)

/-- The first lifted actual circuit realizes its full-register semantic step. -/
lemma firstExponentiationProgram_realizes
    (m ell width N : Nat) (g : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (groupEncoding m ell width)
      (firstExponentiationProgram m ell width N g) environment
      (firstExponentiationStep m ell width N g) := by
  exact UnitaryCircuit.Realizes.onBinaryMiddle
    (left := BinaryLabelEncoding.finIdentity (ell + m))
    (middle := BinaryLabelEncoding.finIdentity ell)
    (right := workspaceEncoding width)
    (exponentiationRaw_realizes (ell + m) width N g)

/-- Full-register action of the second lifted exponentiation. -/
def secondExponentiationStep (m ell width N : Nat) (x : (ZMod N)ˣ)
    (input : GroupRegisters m ell width) :
    GroupRegisters m ell width :=
  let updated := exponentiationRawStep ell width N x⁻¹
    (input.1.2, input.2)
  ((input.1.1, updated.1), updated.2)

/-- The reassociated second actual circuit realizes its full-register step. -/
lemma secondExponentiationProgram_realizes
    (m ell width N : Nat) (x : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (groupEncoding m ell width)
      (secondExponentiationProgram m ell width N x) environment
      (secondExponentiationStep m ell width N x) := by
  constructor
  intro input
  rcases input with ⟨⟨a, b⟩, workspace⟩
  let hwidth :=
    (Nat.add_assoc
      (firstBits (registerParameters m ell width)) ell
      (workspaceBits width)).symm
  let rawProgram :=
    UnitaryCircuit.prodRight
      (m := firstBits (registerParameters m ell width))
      (exponentiationProgram ell width N x⁻¹)
  let rawInput :
      Fin (2 ^ firstBits (registerParameters m ell width)) ×
        (Fin (2 ^ ell) × WorkspaceRegisters width) :=
    (a, (b, workspace))
  let updated := exponentiationRawStep ell width N x⁻¹ (b, workspace)
  let rawOutput :
      Fin (2 ^ firstBits (registerParameters m ell width)) ×
        (Fin (2 ^ ell) × WorkspaceRegisters width) :=
    (a, updated)
  have hraw :=
    (UnitaryCircuit.Realizes.onBinarySuffix
      (left := BinaryLabelEncoding.finIdentity
        (firstBits (registerParameters m ell width)))
      (exponentiationRaw_realizes (environment := environment) ell width N x⁻¹)).apply_encoded_ket
        rawInput
  have hcast := applyNormalized_castProgram (environment := environment) hwidth rawProgram
    ((BinaryLabelEncoding.prod
      (BinaryLabelEncoding.finIdentity
        (firstBits (registerParameters m ell width)))
      (exponentiationEncoding ell width)).encode rawInput)
    ((BinaryLabelEncoding.prod
      (BinaryLabelEncoding.finIdentity
        (firstBits (registerParameters m ell width)))
      (exponentiationEncoding ell width)).encode rawOutput)
    hraw
  have hinput :
      castLabel hwidth
          (prodEquiv
            (a, prodEquiv
              (b, (workspaceEncoding width).encode workspace))) =
        (groupEncoding m ell width).encode ((a, b), workspace) :=
    castLabel_prodEquiv hwidth a b
      ((workspaceEncoding width).encode workspace)
  have houtput :
      castLabel hwidth
          (prodEquiv
            (a, prodEquiv
              (updated.1,
                (workspaceEncoding width).encode updated.2))) =
        (groupEncoding m ell width).encode
          ((a, updated.1), updated.2) :=
    castLabel_prodEquiv hwidth a updated.1
      ((workspaceEncoding width).encode updated.2)
  change
    (castProgram hwidth rawProgram).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv.symm
            ((groupEncoding m ell width).encode ((a, b), workspace)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv.symm
          ((groupEncoding m ell width).encode
            ((a, updated.1), updated.2)))
  rw [← hinput, ← houtput]
  change
    (castProgram hwidth rawProgram).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv.symm
            (castLabel hwidth
              (prodEquiv
                (a, prodEquiv
                  (b, (workspaceEncoding width).encode workspace)))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv.symm
          (castLabel hwidth
            (prodEquiv
              (a, prodEquiv
                (updated.1,
                  (workspaceEncoding width).encode updated.2))))) at hcast
  exact hcast

/-- Full-register semantic action of the two actual exponentiation circuits. -/
def compiledGroupActionStep (m ell width N : Nat)
    (g x : (ZMod N)ˣ) (input : GroupRegisters m ell width) :
    GroupRegisters m ell width :=
  secondExponentiationStep m ell width N x
    (firstExponentiationStep m ell width N g input)

/-- The exact composed circuit realizes its full-register semantic action. -/
lemma compiledGroupActionProgram_realizes
    (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (groupEncoding m ell width)
      (compiledGroupActionProgram m ell width N g x) environment
      (compiledGroupActionStep m ell width N g x) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.seq
      (firstExponentiationProgram_realizes m ell width N g)
      (secondExponentiationProgram_realizes m ell width N x))
  intro input
  rfl

/-- The complete two-program circuit has the required clean basis action. -/
lemma compiledGroupActionProgram_applyLabel_clean
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (a : Fin (2 ^ firstBits (registerParameters m ell width)))
    (b : Fin (2 ^ ell)) (value : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    (compiledGroupActionProgram m ell width N g x).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv.symm
            (cleanLabel m ell width N a b value))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv.symm
          (cleanLabel m ell width N a b
            (oracleValue g x a.val b.val * value))) := by
  let input : GroupRegisters m ell width :=
    ((a, b), cleanWorkspace width N value)
  have haction :=
    (compiledGroupActionProgram_realizes (environment := environment)
      m ell width N g x).apply_encoded_ket input
  have hstep :
      compiledGroupActionStep m ell width N g x input =
        ((a, b), cleanWorkspace width N
          (oracleValue g x a.val b.val * value)) := by
    simp only [input, compiledGroupActionStep, firstExponentiationStep,
      secondExponentiationStep]
    rw [exponentiationRawStep_cleanEndpoint
        (firstBits (registerParameters m ell width)) width N
        g value a hNgtOne hN,
      exponentiationRawStep_cleanEndpoint ell width N
        x⁻¹ (g ^ a.val * value) b hNgtOne hN]
    apply congrArg (fun result : (ZMod N)ˣ =>
      ((a, b), cleanWorkspace width N result))
    simp only [oracleValue, inv_pow]
    ac_rfl
  rw [hstep] at haction
  exact haction

end

end QuantumAlg.ShortDLP.CompiledMAU
