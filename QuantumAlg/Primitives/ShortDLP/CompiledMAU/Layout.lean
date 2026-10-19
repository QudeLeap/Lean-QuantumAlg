/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
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

@[simp] lemma cleanLabel_eq_tripleIndex (m ell width N : Nat)
    (a : Fin (2 ^ firstBits (registerParameters m ell width)))
    (b : Fin (2 ^ ell)) (value : (ZMod N)ˣ) :
    cleanLabel m ell width N a b value =
      tripleIndex (registerParameters m ell width) a b (cleanUnitLabel width N value) := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU
