/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Model
public import QuantumAlg.Components.Classical.Model.BitWord.Semantics

/-!
# The built-in bit and word native language

This selection grants the width-indexed bit/word catalog and explicit uniform
random-bit generation. Native shapes, semantics and coordinates come from the
same typed token. Oracle access remains an independent declaration.
-/

namespace QuantumAlg.BitWord

/-- The existing bit/word machine as one selectable classical native model. -/
@[expose, implicit_reducible]
public noncomputable def model : ClassicalOpModel where
  Token := (input : CShape) × (output : CShape) × Token input output
  Coordinate := Resource.ClassicalOpLabel
  coordinateDecidableEq := inferInstance
  inputShape token := token.1
  outputShape token := token.2.1
  evaluate token := token.2.2.distribution
  coordinate token := token.2.2.coordinate

end QuantumAlg.BitWord
