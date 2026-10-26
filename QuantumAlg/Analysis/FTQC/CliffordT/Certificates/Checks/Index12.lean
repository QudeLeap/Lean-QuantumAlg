/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word12Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word12State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word12Step0 :
    word12Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word12State1 := by decide +kernel

private def word12Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word12State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word12Step1 :
    word12Chunk1.foldl (fun acc a => a.applyPacked acc)
      word12State1 = word12State2 := by decide +kernel

private def word12Chunk2 : List Letter := [.h, .s, .s, .s, .h, .s, .s, .h]
private def word12State3 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word12Step2 :
    word12Chunk2.foldl (fun acc a => a.applyPacked acc)
      word12State2 = word12State3 := by decide +kernel

private def word12Chunk3 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word12State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word12Step3 :
    word12Chunk3.foldl (fun acc a => a.applyPacked acc)
      word12State3 = word12State4 := by decide +kernel

private def word12Chunk4 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word12State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word12Step4 :
    word12Chunk4.foldl (fun acc a => a.applyPacked acc)
      word12State4 = word12State5 := by decide +kernel

private def word12Chunk5 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word12State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((9 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word12Step5 :
    word12Chunk5.foldl (fun acc a => a.applyPacked acc)
      word12State5 = word12State6 := by decide +kernel

private def word12Chunk6 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word12State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word12Step6 :
    word12Chunk6.foldl (fun acc a => a.applyPacked acc)
      word12State6 = word12State7 := by decide +kernel

private def word12Chunk7 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word12State8 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word12Step7 :
    word12Chunk7.foldl (fun acc a => a.applyPacked acc)
      word12State7 = word12State8 := by decide +kernel

private def word12Chunk8 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word12State9 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 6),
        ((21 : Dyadic) * half ^ 6)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 6)⟩,
       ⟨((-31 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 6),
        ((-9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word12Step8 :
    word12Chunk8.foldl (fun acc a => a.applyPacked acc)
      word12State8 = word12State9 := by decide +kernel

private def word12Chunk9 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word12State10 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 5)⟩,
       ⟨((33 : Dyadic) * half ^ 7),
        ((-29 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 7),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((-51 : Dyadic) * half ^ 7),
        ((-23 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-51 : Dyadic) * half ^ 7),
        ((-23 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 7),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 7),
        ((29 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word12Step9 :
    word12Chunk9.foldl (fun acc a => a.applyPacked acc)
      word12State9 = word12State10 := by decide +kernel

private def word12Chunk10 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word12State11 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((-27 : Dyadic) * half ^ 7),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((53 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 8)⟩,
       ⟨((-17 : Dyadic) * half ^ 6),
        ((-27 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-53 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 8)⟩,
       ⟨((-17 : Dyadic) * half ^ 6),
        ((-27 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((27 : Dyadic) * half ^ 7),
        ((-9 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word12Step10 :
    word12Chunk10.foldl (fun acc a => a.applyPacked acc)
      word12State10 = word12State11 := by decide +kernel

private def word12Chunk11 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word12State12 : PackedMat2 :=
    ⟨⟨⟨((-55 : Dyadic) * half ^ 7),
        ((-139 : Dyadic) * half ^ 9)⟩,
       ⟨((-11 : Dyadic) * half ^ 7),
        ((-127 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 8)⟩,
       ⟨((-135 : Dyadic) * half ^ 8),
        ((31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((55 : Dyadic) * half ^ 8),
        ((-39 : Dyadic) * half ^ 9)⟩,
       ⟨((-69 : Dyadic) * half ^ 8),
        ((231 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((133 : Dyadic) * half ^ 8),
        ((33 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word12Step11 :
    word12Chunk11.foldl (fun acc a => a.applyPacked acc)
      word12State11 = word12State12 := by decide +kernel

private def word12Chunk12 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word12State13 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 7),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((-27 : Dyadic) * half ^ 7),
        ((-65 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-75 : Dyadic) * half ^ 9),
        ((-101 : Dyadic) * half ^ 9)⟩,
       ⟨((-49 : Dyadic) * half ^ 9),
        ((307 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-49 : Dyadic) * half ^ 9),
        ((307 : Dyadic) * half ^ 9)⟩,
       ⟨((-75 : Dyadic) * half ^ 9),
        ((-101 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 7),
        ((65 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word12Step12 :
    word12Chunk12.foldl (fun acc a => a.applyPacked acc)
      word12State12 = word12State13 := by decide +kernel

private def word12Chunk13 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word12State14 : PackedMat2 :=
    ⟨⟨⟨((331 : Dyadic) * half ^ 9),
        ((57 : Dyadic) * half ^ 10)⟩,
       ⟨((-9 : Dyadic) * half ^ 7),
        ((-141 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-295 : Dyadic) * half ^ 10),
        ((161 : Dyadic) * half ^ 9)⟩,
       ⟨((149 : Dyadic) * half ^ 10),
        ((31 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((37 : Dyadic) * half ^ 9),
        ((-111 : Dyadic) * half ^ 9)⟩,
       ⟨((-285 : Dyadic) * half ^ 9),
        ((73 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-339 : Dyadic) * half ^ 10),
        ((-367 : Dyadic) * half ^ 10)⟩,
       ⟨((-225 : Dyadic) * half ^ 10),
        ((295 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word12Step13 :
    word12Chunk13.foldl (fun acc a => a.applyPacked acc)
      word12State13 = word12State14 := by decide +kernel

private def word12Chunk14 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word12State15 : PackedMat2 :=
    ⟨⟨⟨((335 : Dyadic) * half ^ 11),
        ((149 : Dyadic) * half ^ 8)⟩,
       ⟨((-197 : Dyadic) * half ^ 11),
        ((307 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((567 : Dyadic) * half ^ 11),
        ((-261 : Dyadic) * half ^ 11)⟩,
       ⟨((-461 : Dyadic) * half ^ 11),
        ((207 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-461 : Dyadic) * half ^ 11),
        ((207 : Dyadic) * half ^ 10)⟩,
       ⟨((567 : Dyadic) * half ^ 11),
        ((-261 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((197 : Dyadic) * half ^ 11),
        ((-307 : Dyadic) * half ^ 11)⟩,
       ⟨((-335 : Dyadic) * half ^ 11),
        ((-149 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word12Step14 :
    word12Chunk14.foldl (fun acc a => a.applyPacked acc)
      word12State14 = word12State15 := by decide +kernel

private def word12Chunk15 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word12State16 : PackedMat2 :=
    ⟨⟨⟨((607 : Dyadic) * half ^ 10),
        ((-25 : Dyadic) * half ^ 12)⟩,
       ⟨((203 : Dyadic) * half ^ 9),
        ((481 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((719 : Dyadic) * half ^ 11),
        ((111 : Dyadic) * half ^ 11)⟩,
       ⟨((285 : Dyadic) * half ^ 9),
        ((-57 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((117 : Dyadic) * half ^ 11),
        ((-1859 : Dyadic) * half ^ 12)⟩,
       ⟨((-339 : Dyadic) * half ^ 11),
        ((421 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((57 : Dyadic) * half ^ 9),
        ((1013 : Dyadic) * half ^ 11)⟩,
       ⟨((-253 : Dyadic) * half ^ 11),
        ((201 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word12Step15 :
    word12Chunk15.foldl (fun acc a => a.applyPacked acc)
      word12State15 = word12State16 := by decide +kernel

private def word12Chunk16 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word12State17 : PackedMat2 :=
    ⟨⟨⟨((303 : Dyadic) * half ^ 12),
        ((1491 : Dyadic) * half ^ 13)⟩,
       ⟨((1207 : Dyadic) * half ^ 11),
        ((1821 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-865 : Dyadic) * half ^ 11),
        ((1413 : Dyadic) * half ^ 13)⟩,
       ⟨((-951 : Dyadic) * half ^ 12),
        ((2527 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-557 : Dyadic) * half ^ 12),
        ((-779 : Dyadic) * half ^ 13)⟩,
       ⟨((-985 : Dyadic) * half ^ 11),
        ((2681 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((165 : Dyadic) * half ^ 12),
        ((2111 : Dyadic) * half ^ 13)⟩,
       ⟨((207 : Dyadic) * half ^ 9),
        ((2717 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word12Step16 :
    word12Chunk16.foldl (fun acc a => a.applyPacked acc)
      word12State16 = word12State17 := by decide +kernel

private def word12Chunk17 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word12State18 : PackedMat2 :=
    ⟨⟨⟨((-743 : Dyadic) * half ^ 13),
        ((-1297 : Dyadic) * half ^ 14)⟩,
       ⟨((-911 : Dyadic) * half ^ 12),
        ((3543 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4543 : Dyadic) * half ^ 13),
        ((3073 : Dyadic) * half ^ 14)⟩,
       ⟨((2359 : Dyadic) * half ^ 12),
        ((4123 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((4543 : Dyadic) * half ^ 13),
        ((-3073 : Dyadic) * half ^ 14)⟩,
       ⟨((2359 : Dyadic) * half ^ 12),
        ((4123 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-743 : Dyadic) * half ^ 13),
        ((-1297 : Dyadic) * half ^ 14)⟩,
       ⟨((911 : Dyadic) * half ^ 12),
        ((-3543 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word12Step17 :
    word12Chunk17.foldl (fun acc a => a.applyPacked acc)
      word12State17 = word12State18 := by decide +kernel

private def word12Chunk18 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word12State19 : PackedMat2 :=
    ⟨⟨⟨((-7109 : Dyadic) * half ^ 14),
        ((-3029 : Dyadic) * half ^ 13)⟩,
       ⟨((-3297 : Dyadic) * half ^ 14),
        ((687 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-7543 : Dyadic) * half ^ 14),
        ((2681 : Dyadic) * half ^ 14)⟩,
       ⟨((4573 : Dyadic) * half ^ 14),
        ((-1125 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1819 : Dyadic) * half ^ 14),
        ((1485 : Dyadic) * half ^ 14)⟩,
       ⟨((-7181 : Dyadic) * half ^ 14),
        ((3029 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-5371 : Dyadic) * half ^ 14),
        ((-5203 : Dyadic) * half ^ 14)⟩,
       ⟨((-6745 : Dyadic) * half ^ 14),
        ((-953 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word12Step18 :
    word12Chunk18.foldl (fun acc a => a.applyPacked acc)
      word12State18 = word12State19 := by decide +kernel

private def word12Chunk19 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word12State20 : PackedMat2 :=
    ⟨⟨⟨((-11659 : Dyadic) * half ^ 15),
        ((509 : Dyadic) * half ^ 11)⟩,
       ⟨((4949 : Dyadic) * half ^ 15),
        ((-4167 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-11543 : Dyadic) * half ^ 15),
        ((-8749 : Dyadic) * half ^ 15)⟩,
       ⟨((-963 : Dyadic) * half ^ 15),
        ((-1893 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-963 : Dyadic) * half ^ 15),
        ((-1893 : Dyadic) * half ^ 12)⟩,
       ⟨((-11543 : Dyadic) * half ^ 15),
        ((-8749 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-4949 : Dyadic) * half ^ 15),
        ((4167 : Dyadic) * half ^ 15)⟩,
       ⟨((11659 : Dyadic) * half ^ 15),
        ((-509 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word12Step19 :
    word12Chunk19.foldl (fun acc a => a.applyPacked acc)
      word12State19 = word12State20 := by decide +kernel

private def word12Chunk20 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word12State21 : PackedMat2 :=
    ⟨⟨⟨((1101 : Dyadic) * half ^ 11),
        ((-1239 : Dyadic) * half ^ 16)⟩,
       ⟨((-6597 : Dyadic) * half ^ 14),
        ((18383 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-6279 : Dyadic) * half ^ 15),
        ((123 : Dyadic) * half ^ 15)⟩,
       ⟨((-1845 : Dyadic) * half ^ 12),
        ((-563 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((8885 : Dyadic) * half ^ 15),
        ((21039 : Dyadic) * half ^ 16)⟩,
       ⟨((-9131 : Dyadic) * half ^ 15),
        ((-8481 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2143 : Dyadic) * half ^ 13),
        ((2211 : Dyadic) * half ^ 15)⟩,
       ⟨((-9811 : Dyadic) * half ^ 15),
        ((15405 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word12Step20 :
    word12Chunk20.foldl (fun acc a => a.applyPacked acc)
      word12State20 = word12State21 := by decide +kernel

private def word12Chunk21 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word12State22 : PackedMat2 :=
    ⟨⟨⟨((1487 : Dyadic) * half ^ 13),
        ((1533 : Dyadic) * half ^ 16)⟩,
       ⟨((5 : Dyadic) * half ^ 9),
        ((11031 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-5199 : Dyadic) * half ^ 16),
        ((-4143 : Dyadic) * half ^ 16)⟩,
       ⟨((-10251 : Dyadic) * half ^ 16),
        ((6635 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((10251 : Dyadic) * half ^ 16),
        ((-6635 : Dyadic) * half ^ 16)⟩,
       ⟨((5199 : Dyadic) * half ^ 16),
        ((4143 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 9),
        ((11031 : Dyadic) * half ^ 14)⟩,
       ⟨((1487 : Dyadic) * half ^ 13),
        ((1533 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word12Step21 :
    word12Chunk21.foldl (fun acc a => a.applyPacked acc)
      word12State21 = word12State22 := by decide +kernel

private def word12Chunk22 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word12State23 : PackedMat2 :=
    ⟨⟨⟨((-5943 : Dyadic) * half ^ 14),
        ((14457 : Dyadic) * half ^ 16)⟩,
       ⟨((-2485 : Dyadic) * half ^ 16),
        ((42957 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((78623 : Dyadic) * half ^ 17),
        ((5973 : Dyadic) * half ^ 15)⟩,
       ⟨((46149 : Dyadic) * half ^ 17),
        ((-3145 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-15091 : Dyadic) * half ^ 16),
        ((-16237 : Dyadic) * half ^ 17)⟩,
       ⟨((8801 : Dyadic) * half ^ 16),
        ((31193 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-14043 : Dyadic) * half ^ 17),
        ((-21287 : Dyadic) * half ^ 17)⟩,
       ⟨((-71871 : Dyadic) * half ^ 17),
        ((26257 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word12Step22 :
    word12Chunk22.foldl (fun acc a => a.applyPacked acc)
      word12State22 = word12State23 := by decide +kernel

private def word12Chunk23 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word12State24 : PackedMat2 :=
    ⟨⟨⟨((-61693 : Dyadic) * half ^ 17),
        ((-37269 : Dyadic) * half ^ 18)⟩,
       ⟨((22271 : Dyadic) * half ^ 15),
        ((-2783 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((106485 : Dyadic) * half ^ 18),
        ((-14415 : Dyadic) * half ^ 17)⟩,
       ⟨((8557 : Dyadic) * half ^ 18),
        ((13289 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-40993 : Dyadic) * half ^ 17),
        ((12241 : Dyadic) * half ^ 16)⟩,
       ⟨((-12163 : Dyadic) * half ^ 17),
        ((-57521 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((26137 : Dyadic) * half ^ 18),
        ((150777 : Dyadic) * half ^ 18)⟩,
       ⟨((-48401 : Dyadic) * half ^ 18),
        ((27391 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word12Step23 :
    word12Chunk23.foldl (fun acc a => a.applyPacked acc)
      word12State23 = word12State24 := by decide +kernel

private def word12Chunk24 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word12State25 : PackedMat2 :=
    ⟨⟨⟨((-21051 : Dyadic) * half ^ 18),
        ((46017 : Dyadic) * half ^ 19)⟩,
       ⟨((88265 : Dyadic) * half ^ 18),
        ((-141775 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-5951 : Dyadic) * half ^ 16),
        ((-51305 : Dyadic) * half ^ 18)⟩,
       ⟨((38047 : Dyadic) * half ^ 18),
        ((145083 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-5951 : Dyadic) * half ^ 16),
        ((-51305 : Dyadic) * half ^ 18)⟩,
       ⟨((-38047 : Dyadic) * half ^ 18),
        ((-145083 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((21051 : Dyadic) * half ^ 18),
        ((-46017 : Dyadic) * half ^ 19)⟩,
       ⟨((88265 : Dyadic) * half ^ 18),
        ((-141775 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word12Step24 :
    word12Chunk24.foldl (fun acc a => a.applyPacked acc)
      word12State24 = word12State25 := by decide +kernel

private def word12Chunk25 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word12State26 : PackedMat2 :=
    ⟨⟨⟨((232895 : Dyadic) * half ^ 19),
        ((-106929 : Dyadic) * half ^ 20)⟩,
       ⟨((-42611 : Dyadic) * half ^ 19),
        ((-625305 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-39815 : Dyadic) * half ^ 18),
        ((-1917 : Dyadic) * half ^ 16)⟩,
       ⟨((99535 : Dyadic) * half ^ 19),
        ((-10509 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((18177 : Dyadic) * half ^ 18),
        ((-19905 : Dyadic) * half ^ 20)⟩,
       ⟨((-2841 : Dyadic) * half ^ 18),
        ((179165 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-366117 : Dyadic) * half ^ 19),
        ((47571 : Dyadic) * half ^ 18)⟩,
       ⟨((64797 : Dyadic) * half ^ 17),
        ((137753 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word12Step25 :
    word12Chunk25.foldl (fun acc a => a.applyPacked acc)
      word12State25 = word12State26 := by decide +kernel

private def word12Chunk26 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word12State27 : PackedMat2 :=
    ⟨⟨⟨((-35987 : Dyadic) * half ^ 18),
        ((1060423 : Dyadic) * half ^ 21)⟩,
       ⟨((-491945 : Dyadic) * half ^ 20),
        ((-150115 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-181551 : Dyadic) * half ^ 19),
        ((-10295 : Dyadic) * half ^ 21)⟩,
       ⟨((-164277 : Dyadic) * half ^ 20),
        ((-456907 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-181551 : Dyadic) * half ^ 19),
        ((-10295 : Dyadic) * half ^ 21)⟩,
       ⟨((164277 : Dyadic) * half ^ 20),
        ((456907 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((35987 : Dyadic) * half ^ 18),
        ((-1060423 : Dyadic) * half ^ 21)⟩,
       ⟨((-491945 : Dyadic) * half ^ 20),
        ((-150115 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word12Step26 :
    word12Chunk26.foldl (fun acc a => a.applyPacked acc)
      word12State26 = word12State27 := by decide +kernel

private def word12Chunk27 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word12State28 : PackedMat2 :=
    ⟨⟨⟨((-986685 : Dyadic) * half ^ 21),
        ((719117 : Dyadic) * half ^ 21)⟩,
       ⟨((-483379 : Dyadic) * half ^ 21),
        ((-21237 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((967713 : Dyadic) * half ^ 21),
        ((253799 : Dyadic) * half ^ 20)⟩,
       ⟨((-252177 : Dyadic) * half ^ 21),
        ((-540131 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-32533 : Dyadic) * half ^ 21),
        ((44721 : Dyadic) * half ^ 18)⟩,
       ⟨((1047729 : Dyadic) * half ^ 21),
        ((609945 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-549221 : Dyadic) * half ^ 21),
        ((91879 : Dyadic) * half ^ 18)⟩,
       ⟨((-889013 : Dyadic) * half ^ 21),
        ((251653 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word12Step27 :
    word12Chunk27.foldl (fun acc a => a.applyPacked acc)
      word12State27 = word12State28 := by decide +kernel

private def word12Chunk28 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word12State29 : PackedMat2 :=
    ⟨⟨⟨((1663395 : Dyadic) * half ^ 21),
        ((-73319 : Dyadic) * half ^ 20)⟩,
       ⟨((74523 : Dyadic) * half ^ 20),
        ((21691 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((659439 : Dyadic) * half ^ 21),
        ((-76639 : Dyadic) * half ^ 22)⟩,
       ⟨((351989 : Dyadic) * half ^ 21),
        ((1235601 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-659439 : Dyadic) * half ^ 21),
        ((76639 : Dyadic) * half ^ 22)⟩,
       ⟨((351989 : Dyadic) * half ^ 21),
        ((1235601 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1663395 : Dyadic) * half ^ 21),
        ((-73319 : Dyadic) * half ^ 20)⟩,
       ⟨((-74523 : Dyadic) * half ^ 20),
        ((-21691 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word12Step28 :
    word12Chunk28.foldl (fun acc a => a.applyPacked acc)
      word12State28 = word12State29 := by decide +kernel

private def word12Chunk29 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word12State30 : PackedMat2 :=
    ⟨⟨⟨((-1223789 : Dyadic) * half ^ 22),
        ((-803459 : Dyadic) * half ^ 23)⟩,
       ⟨((-667229 : Dyadic) * half ^ 22),
        ((3389371 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((2804585 : Dyadic) * half ^ 22),
        ((8865 : Dyadic) * half ^ 18)⟩,
       ⟨((134723 : Dyadic) * half ^ 21),
        ((447787 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((518707 : Dyadic) * half ^ 21),
        ((3074031 : Dyadic) * half ^ 23)⟩,
       ⟨((-376867 : Dyadic) * half ^ 21),
        ((2535139 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-323239 : Dyadic) * half ^ 20),
        ((945509 : Dyadic) * half ^ 22)⟩,
       ⟨((2096415 : Dyadic) * half ^ 22),
        ((34785 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word12Step29 :
    word12Chunk29.foldl (fun acc a => a.applyPacked acc)
      word12State29 = word12State30 := by decide +kernel

private def word12Chunk30 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word12State31 : PackedMat2 :=
    ⟨⟨⟨((-101419 : Dyadic) * half ^ 21),
        ((-7628097 : Dyadic) * half ^ 24)⟩,
       ⟨((-639003 : Dyadic) * half ^ 23),
        ((-2421597 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-652995 : Dyadic) * half ^ 23),
        ((7207393 : Dyadic) * half ^ 24)⟩,
       ⟨((421493 : Dyadic) * half ^ 20),
        ((19113 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((652995 : Dyadic) * half ^ 23),
        ((-7207393 : Dyadic) * half ^ 24)⟩,
       ⟨((421493 : Dyadic) * half ^ 20),
        ((19113 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-101419 : Dyadic) * half ^ 21),
        ((-7628097 : Dyadic) * half ^ 24)⟩,
       ⟨((639003 : Dyadic) * half ^ 23),
        ((2421597 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word12Step30 :
    word12Chunk30.foldl (fun acc a => a.applyPacked acc)
      word12State30 = word12State31 := by decide +kernel

private def word12Chunk31 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word12State32 : PackedMat2 :=
    ⟨⟨⟨((-113197 : Dyadic) * half ^ 21),
        ((768907 : Dyadic) * half ^ 23)⟩,
       ⟨((-177447 : Dyadic) * half ^ 21),
        ((-3116033 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((469515 : Dyadic) * half ^ 24),
        ((-9439771 : Dyadic) * half ^ 24)⟩,
       ⟨((227317 : Dyadic) * half ^ 24),
        ((6164413 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1950523 : Dyadic) * half ^ 21),
        ((121099 : Dyadic) * half ^ 24)⟩,
       ⟨((1637679 : Dyadic) * half ^ 23),
        ((-1361 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-4653847 : Dyadic) * half ^ 24),
        ((-32125 : Dyadic) * half ^ 21)⟩,
       ⟨((-1578219 : Dyadic) * half ^ 24),
        ((-72661 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word12Step31 :
    word12Chunk31.foldl (fun acc a => a.applyPacked acc)
      word12State31 = word12State32 := by decide +kernel

private def word12Chunk32 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word12State33 : PackedMat2 :=
    ⟨⟨⟨((-1187699 : Dyadic) * half ^ 24),
        ((9213219 : Dyadic) * half ^ 25)⟩,
       ⟨((-5950199 : Dyadic) * half ^ 24),
        ((-12177705 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1685667 : Dyadic) * half ^ 23),
        ((-2754789 : Dyadic) * half ^ 24)⟩,
       ⟨((-9562569 : Dyadic) * half ^ 24),
        ((2245349 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1685667 : Dyadic) * half ^ 23),
        ((-2754789 : Dyadic) * half ^ 24)⟩,
       ⟨((9562569 : Dyadic) * half ^ 24),
        ((-2245349 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1187699 : Dyadic) * half ^ 24),
        ((-9213219 : Dyadic) * half ^ 25)⟩,
       ⟨((-5950199 : Dyadic) * half ^ 24),
        ((-12177705 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word12Step32 :
    word12Chunk32.foldl (fun acc a => a.applyPacked acc)
      word12State32 = word12State33 := by decide +kernel

private def word12Chunk33 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word12State34 : PackedMat2 :=
    ⟨⟨⟨((6416611 : Dyadic) * half ^ 24),
        ((20660889 : Dyadic) * half ^ 26)⟩,
       ⟨((3789697 : Dyadic) * half ^ 25),
        ((20444261 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-9504365 : Dyadic) * half ^ 25),
        ((9190283 : Dyadic) * half ^ 26)⟩,
       ⟨((2735555 : Dyadic) * half ^ 23),
        ((-23329409 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((9504365 : Dyadic) * half ^ 25),
        ((-9190283 : Dyadic) * half ^ 26)⟩,
       ⟨((2735555 : Dyadic) * half ^ 23),
        ((-23329409 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((6416611 : Dyadic) * half ^ 24),
        ((20660889 : Dyadic) * half ^ 26)⟩,
       ⟨((-3789697 : Dyadic) * half ^ 25),
        ((-20444261 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word12Step33 :
    word12Chunk33.foldl (fun acc a => a.applyPacked acc)
      word12State33 = word12State34 := by decide +kernel

private def word12Chunk34 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word12State35 : PackedMat2 :=
    ⟨⟨⟨((-3558213 : Dyadic) * half ^ 25),
        ((42380331 : Dyadic) * half ^ 27)⟩,
       ⟨((24919845 : Dyadic) * half ^ 26),
        ((24030201 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((23642691 : Dyadic) * half ^ 25),
        ((-5072571 : Dyadic) * half ^ 27)⟩,
       ⟨((2048503 : Dyadic) * half ^ 26),
        ((-28007739 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((23642691 : Dyadic) * half ^ 25),
        ((-5072571 : Dyadic) * half ^ 27)⟩,
       ⟨((-2048503 : Dyadic) * half ^ 26),
        ((28007739 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((3558213 : Dyadic) * half ^ 25),
        ((-42380331 : Dyadic) * half ^ 27)⟩,
       ⟨((24919845 : Dyadic) * half ^ 26),
        ((24030201 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word12Step34 :
    word12Chunk34.foldl (fun acc a => a.applyPacked acc)
      word12State34 = word12State35 := by decide +kernel

private def word12Chunk35 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word12State36 : PackedMat2 :=
    ⟨⟨⟨((1608749 : Dyadic) * half ^ 26),
        ((4072905 : Dyadic) * half ^ 27)⟩,
       ⟨((6989217 : Dyadic) * half ^ 24),
        ((11671779 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3776879 : Dyadic) * half ^ 27),
        ((12059713 : Dyadic) * half ^ 26)⟩,
       ⟨((44982727 : Dyadic) * half ^ 27),
        ((-7543595 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((44982727 : Dyadic) * half ^ 27),
        ((-7543595 : Dyadic) * half ^ 24)⟩,
       ⟨((3776879 : Dyadic) * half ^ 27),
        ((12059713 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-6989217 : Dyadic) * half ^ 24),
        ((-11671779 : Dyadic) * half ^ 25)⟩,
       ⟨((-1608749 : Dyadic) * half ^ 26),
        ((-4072905 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word12Step35 :
    word12Chunk35.foldl (fun acc a => a.applyPacked acc)
      word12State35 = word12State36 := by decide +kernel

private def word12Chunk36 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word12State37 : PackedMat2 :=
    ⟨⟨⟨((-2785199 : Dyadic) * half ^ 28),
        ((-51909189 : Dyadic) * half ^ 27)⟩,
       ⟨((100368609 : Dyadic) * half ^ 28),
        ((84106067 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-52657611 : Dyadic) * half ^ 28),
        ((17438523 : Dyadic) * half ^ 28)⟩,
       ⟨((-120138139 : Dyadic) * half ^ 28),
        ((508041 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-82467771 : Dyadic) * half ^ 28),
        ((86397875 : Dyadic) * half ^ 28)⟩,
       ⟨((47590725 : Dyadic) * half ^ 28),
        ((-4217533 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-19712311 : Dyadic) * half ^ 28),
        ((48791705 : Dyadic) * half ^ 28)⟩,
       ⟨((-187924445 : Dyadic) * half ^ 28),
        ((-6447113 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word12Step36 :
    word12Chunk36.foldl (fun acc a => a.applyPacked acc)
      word12State36 = word12State37 := by decide +kernel

private def word12Chunk37 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word12State38 : PackedMat2 :=
    ⟨⟨⟨((-58212561 : Dyadic) * half ^ 27),
        ((-12325779 : Dyadic) * half ^ 27)⟩,
       ⟨((-121502129 : Dyadic) * half ^ 28),
        ((-18525873 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((61209913 : Dyadic) * half ^ 28),
        ((-152545885 : Dyadic) * half ^ 29)⟩,
       ⟨((24789845 : Dyadic) * half ^ 28),
        ((-218094667 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-46330069 : Dyadic) * half ^ 26),
        ((42999879 : Dyadic) * half ^ 28)⟩,
       ⟨((32774391 : Dyadic) * half ^ 28),
        ((9105017 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((7712913 : Dyadic) * half ^ 25),
        ((237927251 : Dyadic) * half ^ 29)⟩,
       ⟨((-3100047 : Dyadic) * half ^ 26),
        ((-5077007 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word12Step37 :
    word12Chunk37.foldl (fun acc a => a.applyPacked acc)
      word12State37 = word12State38 := by decide +kernel

private def word12Chunk38 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word12State39 : PackedMat2 :=
    ⟨⟨⟨((2963073 : Dyadic) * half ^ 25),
        ((59347915 : Dyadic) * half ^ 30)⟩,
       ⟨((-251738527 : Dyadic) * half ^ 29),
        ((-139761489 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-298837859 : Dyadic) * half ^ 29),
        ((266411001 : Dyadic) * half ^ 30)⟩,
       ⟨((-68327469 : Dyadic) * half ^ 27),
        ((-152269311 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-52335039 : Dyadic) * half ^ 27),
        ((25527983 : Dyadic) * half ^ 30)⟩,
       ⟨((57070845 : Dyadic) * half ^ 29),
        ((-572147735 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((49777351 : Dyadic) * half ^ 28),
        ((299147695 : Dyadic) * half ^ 30)⟩,
       ⟨((40206787 : Dyadic) * half ^ 29),
        ((204329359 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word12Step38 :
    word12Chunk38.foldl (fun acc a => a.applyPacked acc)
      word12State38 = word12State39 := by decide +kernel

private def word12Chunk39 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word12State40 : PackedMat2 :=
    ⟨⟨⟨((119200743 : Dyadic) * half ^ 28),
        ((80260423 : Dyadic) * half ^ 31)⟩,
       ⟨((-178259757 : Dyadic) * half ^ 30),
        ((-640737123 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-133875565 : Dyadic) * half ^ 29),
        ((960592773 : Dyadic) * half ^ 31)⟩,
       ⟨((-306278353 : Dyadic) * half ^ 30),
        ((-341890791 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-133875565 : Dyadic) * half ^ 29),
        ((960592773 : Dyadic) * half ^ 31)⟩,
       ⟨((306278353 : Dyadic) * half ^ 30),
        ((341890791 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-119200743 : Dyadic) * half ^ 28),
        ((-80260423 : Dyadic) * half ^ 31)⟩,
       ⟨((-178259757 : Dyadic) * half ^ 30),
        ((-640737123 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word12Step39 :
    word12Chunk39.foldl (fun acc a => a.applyPacked acc)
      word12State39 = word12State40 := by decide +kernel

private def word12Chunk40 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word12State41 : PackedMat2 :=
    ⟨⟨⟨((-196360801 : Dyadic) * half ^ 30),
        ((388953961 : Dyadic) * half ^ 30)⟩,
       ⟨((18177105 : Dyadic) * half ^ 28),
        ((-425144287 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1627369899 : Dyadic) * half ^ 31),
        ((115362815 : Dyadic) * half ^ 30)⟩,
       ⟨((-329403571 : Dyadic) * half ^ 31),
        ((12373213 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-51494801 : Dyadic) * half ^ 29),
        ((-978386735 : Dyadic) * half ^ 31)⟩,
       ⟨((31934007 : Dyadic) * half ^ 28),
        ((162245791 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((1203052209 : Dyadic) * half ^ 31),
        ((-269069221 : Dyadic) * half ^ 31)⟩,
       ⟨((-352763635 : Dyadic) * half ^ 31),
        ((123652381 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word12Step40 :
    word12Chunk40.foldl (fun acc a => a.applyPacked acc)
      word12State40 = word12State41 := by decide +kernel

private def word12Chunk41 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word12State42 : PackedMat2 :=
    ⟨⟨⟨((-440846863 : Dyadic) * half ^ 32),
        ((53802083 : Dyadic) * half ^ 29)⟩,
       ⟨((-1656336175 : Dyadic) * half ^ 32),
        ((-356553879 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((2565009161 : Dyadic) * half ^ 32),
        ((731309987 : Dyadic) * half ^ 32)⟩,
       ⟨((2295039333 : Dyadic) * half ^ 32),
        ((-247995975 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((260673913 : Dyadic) * half ^ 32),
        ((-2430024247 : Dyadic) * half ^ 32)⟩,
       ⟨((-1723293887 : Dyadic) * half ^ 32),
        ((-67492457 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((73862785 : Dyadic) * half ^ 32),
        ((-1048591519 : Dyadic) * half ^ 32)⟩,
       ⟨((786970543 : Dyadic) * half ^ 32),
        ((37984041 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word12Step41 :
    word12Chunk41.foldl (fun acc a => a.applyPacked acc)
      word12State41 = word12State42 := by decide +kernel

private def word12Chunk42 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word12State43 : PackedMat2 :=
    ⟨⟨⟨((695605087 : Dyadic) * half ^ 33),
        ((-925398745 : Dyadic) * half ^ 32)⟩,
       ⟨((-5061956113 : Dyadic) * half ^ 33),
        ((-1901061241 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2531572397 : Dyadic) * half ^ 33),
        ((-3548101501 : Dyadic) * half ^ 33)⟩,
       ⟨((765120761 : Dyadic) * half ^ 33),
        ((422555127 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((765120761 : Dyadic) * half ^ 33),
        ((422555127 : Dyadic) * half ^ 32)⟩,
       ⟨((2531572397 : Dyadic) * half ^ 33),
        ((-3548101501 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((5061956113 : Dyadic) * half ^ 33),
        ((1901061241 : Dyadic) * half ^ 33)⟩,
       ⟨((-695605087 : Dyadic) * half ^ 33),
        ((925398745 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word12Step42 :
    word12Chunk42.foldl (fun acc a => a.applyPacked acc)
      word12State42 = word12State43 := by decide +kernel

private def word12Chunk43 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word12State44 : PackedMat2 :=
    ⟨⟨⟨((-1516425311 : Dyadic) * half ^ 33),
        ((1739946073 : Dyadic) * half ^ 33)⟩,
       ⟨((-100881537 : Dyadic) * half ^ 32),
        ((-4280550091 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-3955793757 : Dyadic) * half ^ 33),
        ((-1192318457 : Dyadic) * half ^ 34)⟩,
       ⟨((234967087 : Dyadic) * half ^ 33),
        ((-4966156253 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3079237355 : Dyadic) * half ^ 33),
        ((1860413335 : Dyadic) * half ^ 33)⟩,
       ⟨((-943459449 : Dyadic) * half ^ 32),
        ((1047690211 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1270302009 : Dyadic) * half ^ 32),
        ((-1718188385 : Dyadic) * half ^ 34)⟩,
       ⟨((1505124041 : Dyadic) * half ^ 31),
        ((-1314662237 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word12Step43 :
    word12Chunk43.foldl (fun acc a => a.applyPacked acc)
      word12State43 = word12State44 := by decide +kernel

private def word12Chunk44 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word12State45 : PackedMat2 :=
    ⟨⟨⟨((3916622307 : Dyadic) * half ^ 34),
        ((562093307 : Dyadic) * half ^ 35)⟩,
       ⟨((-7016659625 : Dyadic) * half ^ 33),
        ((1884047541 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-612761235 : Dyadic) * half ^ 33),
        ((5615668921 : Dyadic) * half ^ 35)⟩,
       ⟨((-7405524699 : Dyadic) * half ^ 34),
        ((-4202276429 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((4908972675 : Dyadic) * half ^ 34),
        ((6180002229 : Dyadic) * half ^ 35)⟩,
       ⟨((-353348123 : Dyadic) * half ^ 33),
        ((8631047169 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((660977117 : Dyadic) * half ^ 34),
        ((-17949941557 : Dyadic) * half ^ 35)⟩,
       ⟨((152883803 : Dyadic) * half ^ 31),
        ((-10116696943 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word12Step44 :
    word12Chunk44.foldl (fun acc a => a.applyPacked acc)
      word12State44 = word12State45 := by decide +kernel

private def word12Chunk45 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word12State46 : PackedMat2 :=
    ⟨⟨⟨((16861244525 : Dyadic) * half ^ 35),
        ((9853038569 : Dyadic) * half ^ 35)⟩,
       ⟨((20398534451 : Dyadic) * half ^ 35),
        ((-8527160049 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-246649703 : Dyadic) * half ^ 34),
        ((3325328639 : Dyadic) * half ^ 35)⟩,
       ⟨((5401660391 : Dyadic) * half ^ 34),
        ((3415999 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-2450832895 : Dyadic) * half ^ 35),
        ((2824155047 : Dyadic) * half ^ 34)⟩,
       ⟨((4199824383 : Dyadic) * half ^ 35),
        ((40273521 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((9190099309 : Dyadic) * half ^ 34),
        ((-1768644963 : Dyadic) * half ^ 35)⟩,
       ⟨((-165734815 : Dyadic) * half ^ 32),
        ((-1164368093 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word12Step45 :
    word12Chunk45.foldl (fun acc a => a.applyPacked acc)
      word12State45 = word12State46 := by decide +kernel

private def word12Chunk46 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word12State47 : PackedMat2 :=
    ⟨⟨⟨((23930114805 : Dyadic) * half ^ 35),
        ((-12283739673 : Dyadic) * half ^ 36)⟩,
       ⟨((4744267121 : Dyadic) * half ^ 34),
        ((198218633 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((14815741445 : Dyadic) * half ^ 36),
        ((4335331639 : Dyadic) * half ^ 35)⟩,
       ⟨((3070733677 : Dyadic) * half ^ 36),
        ((-1794815487 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((7924962613 : Dyadic) * half ^ 35),
        ((1468125971 : Dyadic) * half ^ 34)⟩,
       ⟨((-745700665 : Dyadic) * half ^ 35),
        ((-8943237561 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((37655724697 : Dyadic) * half ^ 36),
        ((-14441580563 : Dyadic) * half ^ 36)⟩,
       ⟨((13088245351 : Dyadic) * half ^ 36),
        ((33418649047 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word12Step46 :
    word12Chunk46.foldl (fun acc a => a.applyPacked acc)
      word12State46 = word12State47 := by decide +kernel

private def word12Chunk47 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word12State48 : PackedMat2 :=
    ⟨⟨⟨((-28728806385 : Dyadic) * half ^ 37),
        ((3894863483 : Dyadic) * half ^ 34)⟩,
       ⟨((95533465981 : Dyadic) * half ^ 37),
        ((13872590759 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-33589636731 : Dyadic) * half ^ 37),
        ((17139371533 : Dyadic) * half ^ 36)⟩,
       ⟨((19434286033 : Dyadic) * half ^ 37),
        ((37113381979 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((19434286033 : Dyadic) * half ^ 37),
        ((37113381979 : Dyadic) * half ^ 37)⟩,
       ⟨((-33589636731 : Dyadic) * half ^ 37),
        ((17139371533 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-95533465981 : Dyadic) * half ^ 37),
        ((-13872590759 : Dyadic) * half ^ 37)⟩,
       ⟨((28728806385 : Dyadic) * half ^ 37),
        ((-3894863483 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word12Step47 :
    word12Chunk47.foldl (fun acc a => a.applyPacked acc)
      word12State47 = word12State48 := by decide +kernel

private def word12Chunk48 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word12State49 : PackedMat2 :=
    ⟨⟨⟨((-18025144583 : Dyadic) * half ^ 37),
        ((-34556679263 : Dyadic) * half ^ 37)⟩,
       ⟨((-9046968739 : Dyadic) * half ^ 35),
        ((66885024597 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((15918441497 : Dyadic) * half ^ 37),
        ((-8571882527 : Dyadic) * half ^ 38)⟩,
       ⟨((42834312925 : Dyadic) * half ^ 37),
        ((87115358897 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-39271738185 : Dyadic) * half ^ 37),
        ((-29376377211 : Dyadic) * half ^ 37)⟩,
       ⟨((5980452589 : Dyadic) * half ^ 34),
        ((6728967857 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((16164172667 : Dyadic) * half ^ 36),
        ((-54213019539 : Dyadic) * half ^ 38)⟩,
       ⟨((-25360425965 : Dyadic) * half ^ 35),
        ((18162730373 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word12Step48 :
    word12Chunk48.foldl (fun acc a => a.applyPacked acc)
      word12State48 = word12State49 := by decide +kernel

private def word12Chunk49 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word12State50 : PackedMat2 :=
    ⟨⟨⟨((2647454995 : Dyadic) * half ^ 38),
        ((-284012298687 : Dyadic) * half ^ 39)⟩,
       ⟨((994618267 : Dyadic) * half ^ 35),
        ((-12258794127 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((113797570617 : Dyadic) * half ^ 38),
        ((-55097217375 : Dyadic) * half ^ 39)⟩,
       ⟨((34731180117 : Dyadic) * half ^ 36),
        ((51246328259 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-53171772817 : Dyadic) * half ^ 38),
        ((-25127149851 : Dyadic) * half ^ 39)⟩,
       ⟨((962722279 : Dyadic) * half ^ 37),
        ((-252722291085 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((16984594035 : Dyadic) * half ^ 35),
        ((5309491141 : Dyadic) * half ^ 39)⟩,
       ⟨((-148135546407 : Dyadic) * half ^ 38),
        ((10604401131 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word12Step49 :
    word12Chunk49.foldl (fun acc a => a.applyPacked acc)
      word12State49 = word12State50 := by decide +kernel

private def word12Chunk50 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word12State51 : PackedMat2 :=
    ⟨⟨⟨((57072361667 : Dyadic) * half ^ 39),
        ((-69347516335 : Dyadic) * half ^ 40)⟩,
       ⟨((-87806349135 : Dyadic) * half ^ 38),
        ((-306294577095 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((373318682471 : Dyadic) * half ^ 39),
        ((9947417527 : Dyadic) * half ^ 40)⟩,
       ⟨((-83297615831 : Dyadic) * half ^ 38),
        ((321407442981 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-373318682471 : Dyadic) * half ^ 39),
        ((-9947417527 : Dyadic) * half ^ 40)⟩,
       ⟨((-83297615831 : Dyadic) * half ^ 38),
        ((321407442981 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((57072361667 : Dyadic) * half ^ 39),
        ((-69347516335 : Dyadic) * half ^ 40)⟩,
       ⟨((87806349135 : Dyadic) * half ^ 38),
        ((306294577095 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word12Step50 :
    word12Chunk50.foldl (fun acc a => a.applyPacked acc)
      word12State50 = word12State51 := by decide +kernel

private def word12Chunk51 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word12State52 : PackedMat2 :=
    ⟨⟨⟨((-6183103849 : Dyadic) * half ^ 37),
        ((480176607281 : Dyadic) * half ^ 40)⟩,
       ⟨((-207449822841 : Dyadic) * half ^ 39),
        ((-156824090921 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((58069118809 : Dyadic) * half ^ 40),
        ((24068107753 : Dyadic) * half ^ 38)⟩,
       ⟨((506905078737 : Dyadic) * half ^ 40),
        ((-3451432675 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((79291030553 : Dyadic) * half ^ 38),
        ((-56104494991 : Dyadic) * half ^ 38)⟩,
       ⟨((31154815047 : Dyadic) * half ^ 38),
        ((-282487098773 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-793824789123 : Dyadic) * half ^ 40),
        ((-182717407445 : Dyadic) * half ^ 40)⟩,
       ⟨((166528425439 : Dyadic) * half ^ 40),
        ((-232182238237 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word12Step51 :
    word12Chunk51.foldl (fun acc a => a.applyPacked acc)
      word12State51 = word12State52 := by decide +kernel

private def word12Chunk52 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word12State53 : PackedMat2 :=
    ⟨⟨⟨((214799118117 : Dyadic) * half ^ 41),
        ((393030265425 : Dyadic) * half ^ 40)⟩,
       ⟨((-1382808525785 : Dyadic) * half ^ 41),
        ((266298116767 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((220369569007 : Dyadic) * half ^ 41),
        ((391184314215 : Dyadic) * half ^ 40)⟩,
       ⟨((81281649895 : Dyadic) * half ^ 41),
        ((331980958013 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((1114349586443 : Dyadic) * half ^ 41),
        ((150825609451 : Dyadic) * half ^ 41)⟩,
       ⟨((450387670417 : Dyadic) * half ^ 41),
        ((17385989889 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-1052358647617 : Dyadic) * half ^ 41),
        ((292002351917 : Dyadic) * half ^ 40)⟩,
       ⟨((-519762414083 : Dyadic) * half ^ 41),
        ((-798803821951 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word12Step52 :
    word12Chunk52.foldl (fun acc a => a.applyPacked acc)
      word12State52 = word12State53 := by decide +kernel

private def word12Chunk53 : List Letter := [.h, .t, .h, .t, .h, .t, .h]
private def word12State54 : PackedMat2 :=
    ⟨⟨⟨((602653831363 : Dyadic) * half ^ 42),
        ((2683746986377 : Dyadic) * half ^ 42)⟩,
       ⟨((777178358059 : Dyadic) * half ^ 42),
        ((-137983335389 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((67176494839 : Dyadic) * half ^ 42),
        ((-47500955037 : Dyadic) * half ^ 42)⟩,
       ⟨((1294668550133 : Dyadic) * half ^ 42),
        ((-228867227797 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-67176494839 : Dyadic) * half ^ 42),
        ((47500955037 : Dyadic) * half ^ 42)⟩,
       ⟨((1294668550133 : Dyadic) * half ^ 42),
        ((-228867227797 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((602653831363 : Dyadic) * half ^ 42),
        ((2683746986377 : Dyadic) * half ^ 42)⟩,
       ⟨((-777178358059 : Dyadic) * half ^ 42),
        ((137983335389 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word12Step53 :
    word12Chunk53.foldl (fun acc a => a.applyPacked acc)
      word12State53 = word12State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word12_check : check word12 12 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word12 = word12State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word12Chunk0 ++ word12Chunk1 ++ word12Chunk2 ++ word12Chunk3 ++
      word12Chunk4 ++ word12Chunk5 ++ word12Chunk6 ++ word12Chunk7 ++
      word12Chunk8 ++ word12Chunk9 ++ word12Chunk10 ++ word12Chunk11 ++
      word12Chunk12 ++ word12Chunk13 ++ word12Chunk14 ++ word12Chunk15 ++
      word12Chunk16 ++ word12Chunk17 ++ word12Chunk18 ++ word12Chunk19 ++
      word12Chunk20 ++ word12Chunk21 ++ word12Chunk22 ++ word12Chunk23 ++
      word12Chunk24 ++ word12Chunk25 ++ word12Chunk26 ++ word12Chunk27 ++
      word12Chunk28 ++ word12Chunk29 ++ word12Chunk30 ++ word12Chunk31 ++
      word12Chunk32 ++ word12Chunk33 ++ word12Chunk34 ++ word12Chunk35 ++
      word12Chunk36 ++ word12Chunk37 ++ word12Chunk38 ++ word12Chunk39 ++
      word12Chunk40 ++ word12Chunk41 ++ word12Chunk42 ++ word12Chunk43 ++
      word12Chunk44 ++ word12Chunk45 ++ word12Chunk46 ++ word12Chunk47 ++
      word12Chunk48 ++ word12Chunk49 ++ word12Chunk50 ++ word12Chunk51 ++
      word12Chunk52 ++ word12Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word12Step0, word12Step1, word12Step2, word12Step3, word12Step4,
      word12Step5, word12Step6, word12Step7, word12Step8, word12Step9,
      word12Step10, word12Step11, word12Step12, word12Step13, word12Step14,
      word12Step15, word12Step16, word12Step17, word12Step18, word12Step19,
      word12Step20, word12Step21, word12Step22, word12Step23, word12Step24,
      word12Step25, word12Step26, word12Step27, word12Step28, word12Step29,
      word12Step30, word12Step31, word12Step32, word12Step33, word12Step34,
      word12Step35, word12Step36, word12Step37, word12Step38, word12Step39,
      word12Step40, word12Step41, word12Step42, word12Step43, word12Step44,
      word12Step45, word12Step46, word12Step47, word12Step48, word12Step49,
      word12Step50, word12Step51, word12Step52, word12Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
