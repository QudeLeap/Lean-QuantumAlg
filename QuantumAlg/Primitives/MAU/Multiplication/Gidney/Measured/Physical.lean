/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Complete explicit physical frame of the measured multiplier

The original control is followed by the two original big-endian physical
word blocks and exactly three helper/flag systems. Source indices retain
their little-endian arithmetic interpretation. Every port is an actual
bit lens of the same complete `2n+4`-qubit computational register
[G25, main.tex:271-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical

noncomputable section

/-- Complete computational basis labels for the original simultaneous physical frame. -/
abbrev Registers (width : Nat) := Fin (2 ^ (2 * width + 4))

/-- Literal identity encoding of all original control, word, helper and flag systems. -/
def encoding (width : Nat) : BinaryLabelEncoding (Registers width) :=
  BinaryLabelEncoding.finIdentity (2 * width + 4)

private def helperPorts : Fin 2 ⊕ Unit ≃ Fin 3 :=
  (Equiv.sumCongr Fin.revPerm finOneEquiv.symm).trans finSumFinEquiv

private def targetPorts (width : Nat) : Fin width ⊕ (Fin 2 ⊕ Unit) ≃ Fin (width + 3) :=
  (Equiv.sumCongr Fin.revPerm helperPorts).trans finSumFinEquiv

private def wordPorts (width : Nat) :
    Fin width ⊕ (Fin width ⊕ (Fin 2 ⊕ Unit)) ≃ Fin (width + (width + 3)) :=
  (Equiv.sumCongr Fin.revPerm (targetPorts width)).trans finSumFinEquiv

/-- Explicit ordered physical address map, with arithmetic word bits reversed within each block. -/
def ports (width : Nat) : Port width ≃ Fin (2 * width + 4) :=
  ((Equiv.sumCongr finOneEquiv.symm (wordPorts width)).trans finSumFinEquiv).trans
    (finCongr (by omega))

/-- Every original port is the actual addressed bit of the same complete physical register. -/
def layout (width : Nat) : Layout (encoding width) width where
  bit port := BinaryLabelEncoding.finIdentityBit (2 * width + 4) (ports width port)
  distinct := by
    change Function.Injective (ports width)
    exact (ports width).injective

/-- The actual fixed physical circuit uses this complete canonical ordered qubit layout. -/
def qubits (width : Nat) : QubitLayout (encoding width).width :=
  QubitLayout.canonical (2 * width + 4)

/-- The same actual physical encoding has exactly the constant-workspace width. -/
lemma encoding_width (width : Nat) : (encoding width).width = 2 * width + 4 := rfl

/-- Original port identities are the explicit constructed physical addresses. -/
lemma layout_wire (width : Nat) (port : Port width) :
    ((layout width).bit port).wire = ports width port := rfl

/-- No original physical wire is omitted or duplicated by the complete port frame. -/
lemma layout_covers (width : Nat) (wire : Fin (encoding width).width) :
    ∃ port, ((layout width).bit port).wire = wire :=
  (ports width).surjective wire

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical
