/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Exponentiation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Placement

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

/-- Lift the first modular exponentiation across the untouched second exponent
register. -/
def firstExponentiationProgram (m ell width N : Nat)
    (g : (ZMod N)ˣ) :
    UnitaryCircuit
      (Qubits
        (firstBits (registerParameters m ell width) + ell +
          workspaceBits width)) :=
  UnitaryCircuit.insertMiddle
    (leftWidth := firstBits (registerParameters m ell width))
    (middleWidth := ell) (rightWidth := workspaceBits width)
    (exponentiationProgram (ell + m) width N g)

/-- Lift the second modular exponentiation after the first exponent register;
both exponentiations address the same arithmetic workspace. -/
def secondExponentiationProgram (m ell width N : Nat)
    (x : (ZMod N)ˣ) :
    UnitaryCircuit
      (Qubits
        (firstBits (registerParameters m ell width) + ell +
          workspaceBits width)) :=
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
    UnitaryCircuit
      (Qubits
        (firstBits (registerParameters m ell width) + ell +
          workspaceBits width)) :=
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
theorem firstExponentiationProgram_realizes
    (m ell width N : Nat) (g : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (groupEncoding m ell width)
      (firstExponentiationProgram m ell width N g)
      (firstExponentiationStep m ell width N g) := by
  change
    UnitaryCircuit.Realizes
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.finIdentity (ell + m))
          (BinaryLabelEncoding.finIdentity ell))
        (workspaceEncoding width))
      (UnitaryCircuit.insertMiddle
        (leftWidth := ell + m) (middleWidth := ell)
        (rightWidth := workspaceBits width)
        (exponentiationProgram (ell + m) width N g))
      (fun input =>
        let updated := exponentiationRawStep
          (ell + m) width N g (input.1.1, input.2)
        ((updated.1, input.1.2), updated.2))
  exact UnitaryCircuit.Realizes.insertMiddle
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
theorem secondExponentiationProgram_realizes
    (m ell width N : Nat) (x : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (groupEncoding m ell width)
      (secondExponentiationProgram m ell width N x)
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
    (UnitaryCircuit.Realizes.prodRight
      (left := BinaryLabelEncoding.finIdentity
        (firstBits (registerParameters m ell width)))
      (exponentiationRaw_realizes ell width N x⁻¹)).apply_encoded_ket
        rawInput
  have hcast := applyNormalized_castProgram hwidth rawProgram
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
    (castProgram hwidth rawProgram).applyNormalized
        (NormalizedVector.ket
          ((groupEncoding m ell width).encode ((a, b), workspace))) =
      NormalizedVector.ket
        ((groupEncoding m ell width).encode
          ((a, updated.1), updated.2))
  rw [← hinput, ← houtput]
  change
    (castProgram hwidth rawProgram).applyNormalized
        (NormalizedVector.ket
          (castLabel hwidth
            (prodEquiv
              (a, prodEquiv
                (b, (workspaceEncoding width).encode workspace))))) =
      NormalizedVector.ket
        (castLabel hwidth
          (prodEquiv
            (a, prodEquiv
              (updated.1,
                (workspaceEncoding width).encode updated.2)))) at hcast
  exact hcast

/-- Full-register semantic action of the two actual exponentiation circuits. -/
def compiledGroupActionStep (m ell width N : Nat)
    (g x : (ZMod N)ˣ) (input : GroupRegisters m ell width) :
    GroupRegisters m ell width :=
  secondExponentiationStep m ell width N x
    (firstExponentiationStep m ell width N g input)

/-- The exact composed circuit realizes its full-register semantic action. -/
theorem compiledGroupActionProgram_realizes
    (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    UnitaryCircuit.Realizes (groupEncoding m ell width)
      (compiledGroupActionProgram m ell width N g x)
      (compiledGroupActionStep m ell width N g x) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.seq
      (firstExponentiationProgram_realizes m ell width N g)
      (secondExponentiationProgram_realizes m ell width N x))
  intro input
  rfl

/-- The complete two-program circuit has the required clean basis action. -/
theorem compiledGroupActionProgram_applyLabel_clean
    (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (a : Fin (2 ^ firstBits (registerParameters m ell width)))
    (b : Fin (2 ^ ell)) (value : (ZMod N)ˣ)
    (hNgtOne : 1 < N) (hN : N < 2 ^ width) :
    (compiledGroupActionProgram m ell width N g x).applyNormalized
        (NormalizedVector.ket
          (cleanLabel m ell width N a b value)) =
      NormalizedVector.ket
        (cleanLabel m ell width N a b
          (oracleValue g x a.val b.val * value)) := by
  let input : GroupRegisters m ell width :=
    ((a, b), cleanWorkspace width N value)
  have haction :=
    (compiledGroupActionProgram_realizes
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
  calc
    (compiledGroupActionProgram m ell width N g x).applyNormalized
          (NormalizedVector.ket
            (cleanLabel m ell width N a b value)) =
        (compiledGroupActionProgram m ell width N g x).applyNormalized
          (NormalizedVector.ket
            ((groupEncoding m ell width).encode input)) := by
      rfl
    _ = NormalizedVector.ket
          ((groupEncoding m ell width).encode
            (compiledGroupActionStep m ell width N g x input)) := haction
    _ = NormalizedVector.ket
          ((groupEncoding m ell width).encode
            ((a, b), cleanWorkspace width N
              (oracleValue g x a.val b.val * value))) := by
      rw [hstep]
    _ = NormalizedVector.ket
          (cleanLabel m ell width N a b
            (oracleValue g x a.val b.val * value)) := by
      rfl

/-- The first member uses only its exponent and the same declared arithmetic words. -/
theorem firstExponentiationProgram_physical_idx_subset_range (m ell width N : Nat)
    (g : (ZMod N)ˣ) :
    (firstExponentiationProgram m ell width N g).physical_idx ⊆
      List.range (totalQubits (registerParameters m ell width)) :=
  UnitaryCircuit.insertMiddle_physical_idx_subset_range
    (leftWidth := ell + m) (middleWidth := ell) (rightWidth := workspaceBits width)
    (exponentiationProgram (ell + m) width N g)
    (exponentiationProgram_physical_idx_subset_range (ell + m) width N g)

/-- The second member addresses that same workspace after both exponent fields. -/
theorem secondExponentiationProgram_physical_idx_subset_range (m ell width N : Nat)
    (x : (ZMod N)ˣ) :
    (secondExponentiationProgram m ell width N x).physical_idx ⊆
      List.range (totalQubits (registerParameters m ell width)) := by
  intro index member
  unfold secondExponentiationProgram at member
  rw [castProgram_physical_idx] at member
  have shifted := UnitaryCircuit.prodRight_physical_idx_subset_range
    (m := firstBits (registerParameters m ell width))
    (exponentiationProgram ell width N x⁻¹)
    (exponentiationProgram_physical_idx_subset_range ell width N x⁻¹) member
  exact List.mem_range.mpr (by
    have bound := List.mem_range.mp shifted
    change index < ((ell + m) + ell + workspaceBits width)
    change index < (ell + m) + (ell + workspaceBits width) at bound
    omega)

/-- The actual two-member composition retains the one flat shared carrier. -/
theorem compiledGroupActionProgram_physical_idx_subset (m ell width N : Nat)
    (g x : (ZMod N)ˣ) :
    (compiledGroupActionProgram m ell width N g x).physical_idx ⊆
      List.range (totalQubits (registerParameters m ell width)) :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (firstExponentiationProgram_physical_idx_subset_range m ell width N g)
    (secondExponentiationProgram_physical_idx_subset_range m ell width N x)

end

end QuantumAlg.ShortDLP.CompiledMAU
