/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.SourceLayout
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word

/-!
# Exact two-word arithmetic layout shared by the short-DLP exponents

The unchanged two exponent registers share one power word and one zero
auxiliary word. Every public arithmetic width is used exactly, without
rounding odd widths or retaining an old multiplication workspace. The
canonical unit embedding is the residue representative followed by zero
[VBE95, 9511018.tex:372-416; G17, paper.tex:186-211].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

open Nat.FixedWidth

/-- The actual new multiplier uses exactly a power word and one shared auxiliary word. -/
abbrev WorkspaceRegisters (width : Nat) := Fin (2 ^ width) × Fin (2 ^ width)

/-- The shared workspace is the existing actual two-word multiplication encoding. -/
@[implicit_reducible]
def workspaceEncoding (width : Nat) : BinaryLabelEncoding (WorkspaceRegisters width) :=
  MAU.Multiplication.Accumulate.Gidney.encoding width

abbrev workspaceBits (width : Nat) : Nat := (workspaceEncoding width).width

@[simp] theorem workspaceEncoding_width (width : Nat) :
    (workspaceEncoding width).width = workspaceBits width := rfl

/-- Actual workspace width, including the empty and odd-width cases. -/
theorem workspaceBits_eq (width : Nat) : workspaceBits width = 2 * width := by
  change width + width = 2 * width
  omega

/-- A total fallback label outside the admitted fitted-modulus branch. -/
def zeroWorkspace (width : Nat) : WorkspaceRegisters width := (0, 0)

/-- Canonical unit word and zero auxiliary, with no initialized storage supplied by a caller. -/
def cleanWorkspace (width N : Nat) (value : (ZMod N)ˣ) : WorkspaceRegisters width :=
  if positive : 0 < N then
    if fitted : N ≤ 2 ^ width then
      (unitResidueWord ⟨N, Nat.lt_succ_of_le fitted⟩ positive value, 0)
    else zeroWorkspace width
  else zeroWorkspace width

theorem cleanWorkspace_valid (width N : Nat) (positive : 0 < N) (fitted : N ≤ 2 ^ width)
    (value : (ZMod N)ˣ) :
    cleanWorkspace width N value =
      (unitResidueWord ⟨N, Nat.lt_succ_of_le fitted⟩ positive value, 0) := by
  simp only [cleanWorkspace, dif_pos positive, dif_pos fitted]

/-- Actual finite basis label of a canonically embedded unit. -/
def cleanUnitLabel (width N : Nat) (value : (ZMod N)ˣ) : Fin (2 ^ workspaceBits width) :=
  (workspaceEncoding width).encode (cleanWorkspace width N value)

/-- Distinct units remain distinct in the actual two-word layout. -/
theorem cleanUnitLabel_injective (width N : Nat) (nontrivial : 1 < N) (fits : N < 2 ^ width) :
    Function.Injective (cleanUnitLabel width N) := by
  let : NeZero N := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt nontrivial)⟩
  intro left right same
  have encoded : (workspaceEncoding width).encode (cleanWorkspace width N left) =
      (workspaceEncoding width).encode (cleanWorkspace width N right) := same
  have words := (workspaceEncoding width).encode_injective encoded
  rw [cleanWorkspace_valid width N (Nat.zero_lt_of_lt nontrivial) (Nat.le_of_lt fits),
    cleanWorkspace_valid width N (Nat.zero_lt_of_lt nontrivial) (Nat.le_of_lt fits)] at words
  have values := congrArg (fun state : WorkspaceRegisters width => state.1.val) words
  apply Units.ext
  exact ZMod.val_injective N values

/-- The clean unit injection consumed by the unchanged short-DLP Born analysis. -/
def unitEncoding (width N : Nat) (nontrivial : 1 < N) (fits : N < 2 ^ width) :
    UnitEncoding N (workspaceBits width) where
  encode := cleanUnitLabel width N
  encode_injective := cleanUnitLabel_injective width N nontrivial fits

/-- Preserve both source exponent widths and use the actual new arithmetic width. -/
@[implicit_reducible]
def registerParameters (m ell width : Nat) : RegisterParameters where
  m := m
  ell := ell
  workspaceBits := workspaceBits width

/-- Complete live quantum carrier before and after the two source exponentiations. -/
theorem totalQubits_eq (m ell width : Nat) :
    totalQubits (registerParameters m ell width) = m + 2 * ell + 2 * width := by
  change (ell + m) + ell + workspaceBits width = _
  rw [workspaceBits_eq]
  omega

/-- Both exponent fields and the two arithmetic words, without additional systems. -/
abbrev GroupRegisters (m ell width : Nat) :=
  (Fin (2 ^ (ell + m)) × Fin (2 ^ ell)) × WorkspaceRegisters width

/-- Physical word order remains first exponent, second exponent, power, auxiliary. -/
def groupEncoding (m ell width : Nat) : BinaryLabelEncoding (GroupRegisters m ell width) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity (ell + m))
      (BinaryLabelEncoding.finIdentity ell)) (workspaceEncoding width)

/-- The clean group label is shared by the actual compiler and the independent Born model. -/
def cleanLabel (m ell width N : Nat)
    (a : Fin (2 ^ firstBits (registerParameters m ell width)))
    (b : Fin (2 ^ ell)) (value : (ZMod N)ˣ) :
    Fin (2 ^ totalQubits (registerParameters m ell width)) :=
  (groupEncoding m ell width).encode ((a, b), cleanWorkspace width N value)

@[simp] theorem cleanLabel_eq_tripleIndex (m ell width N : Nat)
    (a : Fin (2 ^ firstBits (registerParameters m ell width)))
    (b : Fin (2 ^ ell)) (value : (ZMod N)ˣ) :
    cleanLabel m ell width N a b value =
      tripleIndex (registerParameters m ell width) a b (cleanUnitLabel width N value) := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU
