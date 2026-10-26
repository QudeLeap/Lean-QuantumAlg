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
private def word22Chunk0 : List Letter := [.s, .s, .s, .h, .s, .s, .h, .h]
private def word22State1 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩⟩
private lemma word22Step0 :
    word22Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word22State1 := by decide +kernel

private def word22Chunk1 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word22State2 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word22Step1 :
    word22Chunk1.foldl (fun acc a => a.applyPacked acc)
      word22State1 = word22State2 := by decide +kernel

private def word22Chunk2 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word22State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word22Step2 :
    word22Chunk2.foldl (fun acc a => a.applyPacked acc)
      word22State2 = word22State3 := by decide +kernel

private def word22Chunk3 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word22State4 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word22Step3 :
    word22Chunk3.foldl (fun acc a => a.applyPacked acc)
      word22State3 = word22State4 := by decide +kernel

private def word22Chunk4 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word22State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-11 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩⟩
private lemma word22Step4 :
    word22Chunk4.foldl (fun acc a => a.applyPacked acc)
      word22State4 = word22State5 := by decide +kernel

private def word22Chunk5 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word22State6 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((17 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word22Step5 :
    word22Chunk5.foldl (fun acc a => a.applyPacked acc)
      word22State5 = word22State6 := by decide +kernel

private def word22Chunk6 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word22State7 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word22Step6 :
    word22Chunk6.foldl (fun acc a => a.applyPacked acc)
      word22State6 = word22State7 := by decide +kernel

private def word22Chunk7 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word22State8 : PackedMat2 :=
    ⟨⟨⟨((39 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((-17 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((23 : Dyadic) * half ^ 7)⟩,
       ⟨((5 : Dyadic) * half ^ 6),
        ((-59 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-13 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((-57 : Dyadic) * half ^ 7)⟩,
       ⟨((-11 : Dyadic) * half ^ 6),
        ((21 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word22Step7 :
    word22Chunk7.foldl (fun acc a => a.applyPacked acc)
      word22State7 = word22State8 := by decide +kernel

private def word22Chunk8 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word22State9 : PackedMat2 :=
    ⟨⟨⟨((9 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 6)⟩,
       ⟨((15 : Dyadic) * half ^ 6),
        ((-9 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 5),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((-45 : Dyadic) * half ^ 6),
        ((19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-45 : Dyadic) * half ^ 6),
        ((19 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((23 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 7)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((-9 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word22Step8 :
    word22Chunk8.foldl (fun acc a => a.applyPacked acc)
      word22State8 = word22State9 := by decide +kernel

private def word22Chunk9 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word22State10 : PackedMat2 :=
    ⟨⟨⟨((-59 : Dyadic) * half ^ 8),
        ((27 : Dyadic) * half ^ 7)⟩,
       ⟨((-27 : Dyadic) * half ^ 8),
        ((-15 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((191 : Dyadic) * half ^ 8),
        ((41 : Dyadic) * half ^ 8)⟩,
       ⟨((101 : Dyadic) * half ^ 8),
        ((-25 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 8),
        ((-73 : Dyadic) * half ^ 7)⟩,
       ⟨((-91 : Dyadic) * half ^ 8),
        ((-45 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((39 : Dyadic) * half ^ 8),
        ((-43 : Dyadic) * half ^ 8)⟩,
       ⟨((69 : Dyadic) * half ^ 8),
        ((-1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word22Step9 :
    word22Chunk9.foldl (fun acc a => a.applyPacked acc)
      word22State9 = word22State10 := by decide +kernel

private def word22Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word22State11 : PackedMat2 :=
    ⟨⟨⟨((163 : Dyadic) * half ^ 8),
        ((-3 : Dyadic) * half ^ 9)⟩,
       ⟨((-95 : Dyadic) * half ^ 8),
        ((77 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 6),
        ((187 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((127 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 6),
        ((187 : Dyadic) * half ^ 9)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-127 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-163 : Dyadic) * half ^ 8),
        ((3 : Dyadic) * half ^ 9)⟩,
       ⟨((-95 : Dyadic) * half ^ 8),
        ((77 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word22Step10 :
    word22Chunk10.foldl (fun acc a => a.applyPacked acc)
      word22State10 = word22State11 := by decide +kernel

private def word22Chunk11 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word22State12 : PackedMat2 :=
    ⟨⟨⟨((275 : Dyadic) * half ^ 9),
        ((-199 : Dyadic) * half ^ 10)⟩,
       ⟨((35 : Dyadic) * half ^ 7),
        ((-57 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((77 : Dyadic) * half ^ 7),
        ((109 : Dyadic) * half ^ 10)⟩,
       ⟨((117 : Dyadic) * half ^ 9),
        ((249 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((117 : Dyadic) * half ^ 9),
        ((249 : Dyadic) * half ^ 10)⟩,
       ⟨((77 : Dyadic) * half ^ 7),
        ((109 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 7),
        ((57 : Dyadic) * half ^ 10)⟩,
       ⟨((-275 : Dyadic) * half ^ 9),
        ((199 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word22Step11 :
    word22Chunk11.foldl (fun acc a => a.applyPacked acc)
      word22State11 = word22State12 := by decide +kernel

private def word22Chunk12 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word22State13 : PackedMat2 :=
    ⟨⟨⟨((-307 : Dyadic) * half ^ 10),
        ((51 : Dyadic) * half ^ 7)⟩,
       ⟨((-63 : Dyadic) * half ^ 10),
        ((29 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-367 : Dyadic) * half ^ 10),
        ((-291 : Dyadic) * half ^ 10)⟩,
       ⟨((441 : Dyadic) * half ^ 10),
        ((75 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-441 : Dyadic) * half ^ 10),
        ((-75 : Dyadic) * half ^ 10)⟩,
       ⟨((367 : Dyadic) * half ^ 10),
        ((291 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-63 : Dyadic) * half ^ 10),
        ((29 : Dyadic) * half ^ 7)⟩,
       ⟨((-307 : Dyadic) * half ^ 10),
        ((51 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word22Step12 :
    word22Chunk12.foldl (fun acc a => a.applyPacked acc)
      word22State12 = word22State13 := by decide +kernel

private def word22Chunk13 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word22State14 : PackedMat2 :=
    ⟨⟨⟨((105 : Dyadic) * half ^ 11),
        ((-837 : Dyadic) * half ^ 11)⟩,
       ⟨((763 : Dyadic) * half ^ 11),
        ((141 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-503 : Dyadic) * half ^ 11),
        ((11 : Dyadic) * half ^ 9)⟩,
       ⟨((-1331 : Dyadic) * half ^ 11),
        ((79 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((123 : Dyadic) * half ^ 11),
        ((-917 : Dyadic) * half ^ 11)⟩,
       ⟨((-35 : Dyadic) * half ^ 11),
        ((207 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((555 : Dyadic) * half ^ 11),
        ((-217 : Dyadic) * half ^ 10)⟩,
       ⟨((1119 : Dyadic) * half ^ 11),
        ((329 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word22Step13 :
    word22Chunk13.foldl (fun acc a => a.applyPacked acc)
      word22State13 = word22State14 := by decide +kernel

private def word22Chunk14 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word22State15 : PackedMat2 :=
    ⟨⟨⟨((-471 : Dyadic) * half ^ 9),
        ((-49 : Dyadic) * half ^ 11)⟩,
       ⟨((83 : Dyadic) * half ^ 11),
        ((-15 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 8),
        ((-27 : Dyadic) * half ^ 7)⟩,
       ⟨((-225 : Dyadic) * half ^ 11),
        ((-225 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-41 : Dyadic) * half ^ 8),
        ((27 : Dyadic) * half ^ 7)⟩,
       ⟨((-225 : Dyadic) * half ^ 11),
        ((-225 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-471 : Dyadic) * half ^ 9),
        ((-49 : Dyadic) * half ^ 11)⟩,
       ⟨((-83 : Dyadic) * half ^ 11),
        ((15 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word22Step14 :
    word22Chunk14.foldl (fun acc a => a.applyPacked acc)
      word22State14 = word22State15 := by decide +kernel

private def word22Chunk15 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word22State16 : PackedMat2 :=
    ⟨⟨⟨((119 : Dyadic) * half ^ 10),
        ((-3841 : Dyadic) * half ^ 13)⟩,
       ⟨((-1707 : Dyadic) * half ^ 12),
        ((-485 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-703 : Dyadic) * half ^ 12),
        ((-695 : Dyadic) * half ^ 13)⟩,
       ⟨((-39 : Dyadic) * half ^ 10),
        ((-3281 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1293 : Dyadic) * half ^ 12),
        ((-547 : Dyadic) * half ^ 13)⟩,
       ⟨((497 : Dyadic) * half ^ 10),
        ((859 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((839 : Dyadic) * half ^ 11),
        ((-2183 : Dyadic) * half ^ 13)⟩,
       ⟨((-2163 : Dyadic) * half ^ 12),
        ((-1231 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word22Step15 :
    word22Chunk15.foldl (fun acc a => a.applyPacked acc)
      word22State15 = word22State16 := by decide +kernel

private def word22Chunk16 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word22State17 : PackedMat2 :=
    ⟨⟨⟨((-2837 : Dyadic) * half ^ 13),
        ((371 : Dyadic) * half ^ 13)⟩,
       ⟨((147 : Dyadic) * half ^ 13),
        ((-1987 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1015 : Dyadic) * half ^ 13),
        ((1429 : Dyadic) * half ^ 12)⟩,
       ⟨((-5691 : Dyadic) * half ^ 13),
        ((-373 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-5691 : Dyadic) * half ^ 13),
        ((-373 : Dyadic) * half ^ 12)⟩,
       ⟨((-1015 : Dyadic) * half ^ 13),
        ((1429 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-147 : Dyadic) * half ^ 13),
        ((1987 : Dyadic) * half ^ 13)⟩,
       ⟨((2837 : Dyadic) * half ^ 13),
        ((-371 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word22Step16 :
    word22Chunk16.foldl (fun acc a => a.applyPacked acc)
      word22State16 = word22State17 := by decide +kernel

private def word22Chunk17 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word22State18 : PackedMat2 :=
    ⟨⟨⟨((-3009 : Dyadic) * half ^ 14),
        ((-797 : Dyadic) * half ^ 12)⟩,
       ⟨((-4699 : Dyadic) * half ^ 14),
        ((-2835 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((13765 : Dyadic) * half ^ 14),
        ((-1761 : Dyadic) * half ^ 14)⟩,
       ⟨((-891 : Dyadic) * half ^ 14),
        ((-93 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((3249 : Dyadic) * half ^ 14),
        ((-6437 : Dyadic) * half ^ 14)⟩,
       ⟨((273 : Dyadic) * half ^ 14),
        ((-229 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-6023 : Dyadic) * half ^ 14),
        ((-1927 : Dyadic) * half ^ 13)⟩,
       ⟨((-353 : Dyadic) * half ^ 14),
        ((845 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word22Step17 :
    word22Chunk17.foldl (fun acc a => a.applyPacked acc)
      word22State17 = word22State18 := by decide +kernel

private def word22Chunk18 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word22State19 : PackedMat2 :=
    ⟨⟨⟨((2651 : Dyadic) * half ^ 13),
        ((431 : Dyadic) * half ^ 15)⟩,
       ⟨((-1015 : Dyadic) * half ^ 13),
        ((-11535 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-9585 : Dyadic) * half ^ 14),
        ((6723 : Dyadic) * half ^ 15)⟩,
       ⟨((5527 : Dyadic) * half ^ 14),
        ((7009 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-9585 : Dyadic) * half ^ 14),
        ((6723 : Dyadic) * half ^ 15)⟩,
       ⟨((-5527 : Dyadic) * half ^ 14),
        ((-7009 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2651 : Dyadic) * half ^ 13),
        ((-431 : Dyadic) * half ^ 15)⟩,
       ⟨((-1015 : Dyadic) * half ^ 13),
        ((-11535 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word22Step18 :
    word22Chunk18.foldl (fun acc a => a.applyPacked acc)
      word22State18 = word22State19 := by decide +kernel

private def word22Chunk19 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word22State20 : PackedMat2 :=
    ⟨⟨⟨((4131 : Dyadic) * half ^ 13),
        ((1205 : Dyadic) * half ^ 12)⟩,
       ⟨((617 : Dyadic) * half ^ 14),
        ((-769 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-4219 : Dyadic) * half ^ 14),
        ((1853 : Dyadic) * half ^ 12)⟩,
       ⟨((2817 : Dyadic) * half ^ 14),
        ((-5903 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((8921 : Dyadic) * half ^ 15),
        ((-701 : Dyadic) * half ^ 14)⟩,
       ⟨((20727 : Dyadic) * half ^ 15),
        ((-1759 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-8871 : Dyadic) * half ^ 15),
        ((-8879 : Dyadic) * half ^ 15)⟩,
       ⟨((-10409 : Dyadic) * half ^ 15),
        ((-7645 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word22Step19 :
    word22Chunk19.foldl (fun acc a => a.applyPacked acc)
      word22State19 = word22State20 := by decide +kernel

private def word22Chunk20 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word22State21 : PackedMat2 :=
    ⟨⟨⟨((33479 : Dyadic) * half ^ 16),
        ((11705 : Dyadic) * half ^ 16)⟩,
       ⟨((9733 : Dyadic) * half ^ 16),
        ((19483 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((6709 : Dyadic) * half ^ 16),
        ((-9045 : Dyadic) * half ^ 15)⟩,
       ⟨((22367 : Dyadic) * half ^ 16),
        ((-5143 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-22367 : Dyadic) * half ^ 16),
        ((5143 : Dyadic) * half ^ 14)⟩,
       ⟨((-6709 : Dyadic) * half ^ 16),
        ((9045 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((9733 : Dyadic) * half ^ 16),
        ((19483 : Dyadic) * half ^ 16)⟩,
       ⟨((33479 : Dyadic) * half ^ 16),
        ((11705 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word22Step20 :
    word22Chunk20.foldl (fun acc a => a.applyPacked acc)
      word22State20 = word22State21 := by decide +kernel

private def word22Chunk21 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word22State22 : PackedMat2 :=
    ⟨⟨⟨((-73357 : Dyadic) * half ^ 17),
        ((1257 : Dyadic) * half ^ 17)⟩,
       ⟨((48225 : Dyadic) * half ^ 17),
        ((15959 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-16861 : Dyadic) * half ^ 17),
        ((12579 : Dyadic) * half ^ 15)⟩,
       ⟨((-20841 : Dyadic) * half ^ 17),
        ((28725 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((79041 : Dyadic) * half ^ 17),
        ((-18851 : Dyadic) * half ^ 17)⟩,
       ⟨((21591 : Dyadic) * half ^ 17),
        ((995 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-33175 : Dyadic) * half ^ 17),
        ((6283 : Dyadic) * half ^ 16)⟩,
       ⟨((30661 : Dyadic) * half ^ 17),
        ((60791 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word22Step21 :
    word22Chunk21.foldl (fun acc a => a.applyPacked acc)
      word22State21 = word22State22 := by decide +kernel

private def word22Chunk22 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word22State23 : PackedMat2 :=
    ⟨⟨⟨((-55631 : Dyadic) * half ^ 17),
        ((-38483 : Dyadic) * half ^ 18)⟩,
       ⟨((18941 : Dyadic) * half ^ 16),
        ((-18999 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-12495 : Dyadic) * half ^ 14),
        ((9633 : Dyadic) * half ^ 18)⟩,
       ⟨((-40325 : Dyadic) * half ^ 17),
        ((11363 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-40325 : Dyadic) * half ^ 17),
        ((11363 : Dyadic) * half ^ 18)⟩,
       ⟨((-12495 : Dyadic) * half ^ 14),
        ((9633 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-18941 : Dyadic) * half ^ 16),
        ((18999 : Dyadic) * half ^ 18)⟩,
       ⟨((55631 : Dyadic) * half ^ 17),
        ((38483 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word22Step22 :
    word22Chunk22.foldl (fun acc a => a.applyPacked acc)
      word22State22 = word22State23 := by decide +kernel

private def word22Chunk23 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word22State24 : PackedMat2 :=
    ⟨⟨⟨((18505 : Dyadic) * half ^ 18),
        ((-44079 : Dyadic) * half ^ 17)⟩,
       ⟨((-123119 : Dyadic) * half ^ 18),
        ((-24217 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((168161 : Dyadic) * half ^ 18),
        ((-31441 : Dyadic) * half ^ 18)⟩,
       ⟨((-39395 : Dyadic) * half ^ 18),
        ((-24251 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((13923 : Dyadic) * half ^ 16),
        ((-64383 : Dyadic) * half ^ 18)⟩,
       ⟨((3595 : Dyadic) * half ^ 17),
        ((-51889 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-8537 : Dyadic) * half ^ 14),
        ((-52307 : Dyadic) * half ^ 18)⟩,
       ⟨((-9931 : Dyadic) * half ^ 16),
        ((17703 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word22Step23 :
    word22Chunk23.foldl (fun acc a => a.applyPacked acc)
      word22State23 = word22State24 := by decide +kernel

private def word22Chunk24 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word22State25 : PackedMat2 :=
    ⟨⟨⟨((22481 : Dyadic) * half ^ 16),
        ((-55017 : Dyadic) * half ^ 19)⟩,
       ⟨((-92361 : Dyadic) * half ^ 18),
        ((-65449 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-41801 : Dyadic) * half ^ 17),
        ((-102153 : Dyadic) * half ^ 19)⟩,
       ⟨((-19713 : Dyadic) * half ^ 15),
        ((24861 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-19713 : Dyadic) * half ^ 15),
        ((24861 : Dyadic) * half ^ 17)⟩,
       ⟨((-41801 : Dyadic) * half ^ 17),
        ((-102153 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((92361 : Dyadic) * half ^ 18),
        ((65449 : Dyadic) * half ^ 18)⟩,
       ⟨((-22481 : Dyadic) * half ^ 16),
        ((55017 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word22Step24 :
    word22Chunk24.foldl (fun acc a => a.applyPacked acc)
      word22State24 = word22State25 := by decide +kernel

private def word22Chunk25 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word22State26 : PackedMat2 :=
    ⟨⟨⟨((494063 : Dyadic) * half ^ 20),
        ((-1625 : Dyadic) * half ^ 16)⟩,
       ⟨((86449 : Dyadic) * half ^ 20),
        ((-266047 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-39227 : Dyadic) * half ^ 20),
        ((-573801 : Dyadic) * half ^ 20)⟩,
       ⟨((-101167 : Dyadic) * half ^ 20),
        ((-32957 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((39227 : Dyadic) * half ^ 20),
        ((573801 : Dyadic) * half ^ 20)⟩,
       ⟨((-101167 : Dyadic) * half ^ 20),
        ((-32957 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((494063 : Dyadic) * half ^ 20),
        ((-1625 : Dyadic) * half ^ 16)⟩,
       ⟨((-86449 : Dyadic) * half ^ 20),
        ((266047 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word22Step25 :
    word22Chunk25.foldl (fun acc a => a.applyPacked acc)
      word22State25 = word22State26 := by decide +kernel

private def word22Chunk26 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word22State27 : PackedMat2 :=
    ⟨⟨⟨((-49611 : Dyadic) * half ^ 20),
        ((1333911 : Dyadic) * half ^ 21)⟩,
       ⟨((-69599 : Dyadic) * half ^ 20),
        ((-71379 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-138093 : Dyadic) * half ^ 19),
        ((66601 : Dyadic) * half ^ 21)⟩,
       ⟨((-97333 : Dyadic) * half ^ 19),
        ((-408921 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((237761 : Dyadic) * half ^ 20),
        ((-5095 : Dyadic) * half ^ 17)⟩,
       ⟨((21395 : Dyadic) * half ^ 17),
        ((117713 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-702645 : Dyadic) * half ^ 20),
        ((-4997 : Dyadic) * half ^ 19)⟩,
       ⟨((315633 : Dyadic) * half ^ 19),
        ((-59605 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word22Step26 :
    word22Chunk26.foldl (fun acc a => a.applyPacked acc)
      word22State26 = word22State27 := by decide +kernel

private def word22Chunk27 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word22State28 : PackedMat2 :=
    ⟨⟨⟨((1016521 : Dyadic) * half ^ 21),
        ((-833623 : Dyadic) * half ^ 22)⟩,
       ⟨((57965 : Dyadic) * half ^ 17),
        ((1219479 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((319507 : Dyadic) * half ^ 20),
        ((189421 : Dyadic) * half ^ 22)⟩,
       ⟨((-302291 : Dyadic) * half ^ 21),
        ((1338581 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-302291 : Dyadic) * half ^ 21),
        ((1338581 : Dyadic) * half ^ 22)⟩,
       ⟨((319507 : Dyadic) * half ^ 20),
        ((189421 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-57965 : Dyadic) * half ^ 17),
        ((-1219479 : Dyadic) * half ^ 22)⟩,
       ⟨((-1016521 : Dyadic) * half ^ 21),
        ((833623 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word22Step27 :
    word22Chunk27.foldl (fun acc a => a.applyPacked acc)
      word22State27 = word22State28 := by decide +kernel

private def word22Chunk28 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word22State29 : PackedMat2 :=
    ⟨⟨⟨((-1031677 : Dyadic) * half ^ 21),
        ((134509 : Dyadic) * half ^ 19)⟩,
       ⟨((1437507 : Dyadic) * half ^ 21),
        ((605339 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-27233 : Dyadic) * half ^ 18),
        ((-40001 : Dyadic) * half ^ 18)⟩,
       ⟨((480537 : Dyadic) * half ^ 21),
        ((209231 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((430785 : Dyadic) * half ^ 22),
        ((-262673 : Dyadic) * half ^ 22)⟩,
       ⟨((849247 : Dyadic) * half ^ 22),
        ((698401 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1681411 : Dyadic) * half ^ 22),
        ((202915 : Dyadic) * half ^ 21)⟩,
       ⟨((470733 : Dyadic) * half ^ 22),
        ((-38581 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word22Step28 :
    word22Chunk28.foldl (fun acc a => a.applyPacked acc)
      word22State28 = word22State29 := by decide +kernel

private def word22Chunk29 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word22State30 : PackedMat2 :=
    ⟨⟨⟨((94801 : Dyadic) * half ^ 23),
        ((-3510579 : Dyadic) * half ^ 23)⟩,
       ⟨((-2295883 : Dyadic) * half ^ 23),
        ((542897 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-3437947 : Dyadic) * half ^ 23),
        ((101057 : Dyadic) * half ^ 20)⟩,
       ⟨((-4702601 : Dyadic) * half ^ 23),
        ((-1191913 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-3437947 : Dyadic) * half ^ 23),
        ((101057 : Dyadic) * half ^ 20)⟩,
       ⟨((4702601 : Dyadic) * half ^ 23),
        ((1191913 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-94801 : Dyadic) * half ^ 23),
        ((3510579 : Dyadic) * half ^ 23)⟩,
       ⟨((-2295883 : Dyadic) * half ^ 23),
        ((542897 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word22Step29 :
    word22Chunk29.foldl (fun acc a => a.applyPacked acc)
      word22State29 = word22State30 := by decide +kernel

private def word22Chunk30 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word22State31 : PackedMat2 :=
    ⟨⟨⟨((-40229 : Dyadic) * half ^ 19),
        ((-1799449 : Dyadic) * half ^ 24)⟩,
       ⟨((-609053 : Dyadic) * half ^ 22),
        ((-6998375 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((3207157 : Dyadic) * half ^ 23),
        ((-5756613 : Dyadic) * half ^ 24)⟩,
       ⟨((-1762945 : Dyadic) * half ^ 23),
        ((-4979939 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((388337 : Dyadic) * half ^ 23),
        ((-2485051 : Dyadic) * half ^ 23)⟩,
       ⟨((-1342069 : Dyadic) * half ^ 21),
        ((361053 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((2599463 : Dyadic) * half ^ 23),
        ((287221 : Dyadic) * half ^ 23)⟩,
       ⟨((68733 : Dyadic) * half ^ 17),
        ((930885 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word22Step30 :
    word22Chunk30.foldl (fun acc a => a.applyPacked acc)
      word22State30 = word22State31 := by decide +kernel

private def word22Chunk31 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word22State32 : PackedMat2 :=
    ⟨⟨⟨((-96503 : Dyadic) * half ^ 23),
        ((740945 : Dyadic) * half ^ 25)⟩,
       ⟨((-13010315 : Dyadic) * half ^ 24),
        ((-2791449 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1394205 : Dyadic) * half ^ 24),
        ((11968695 : Dyadic) * half ^ 25)⟩,
       ⟨((1313065 : Dyadic) * half ^ 23),
        ((-7420733 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1313065 : Dyadic) * half ^ 23),
        ((7420733 : Dyadic) * half ^ 25)⟩,
       ⟨((1394205 : Dyadic) * half ^ 24),
        ((-11968695 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-13010315 : Dyadic) * half ^ 24),
        ((-2791449 : Dyadic) * half ^ 25)⟩,
       ⟨((-96503 : Dyadic) * half ^ 23),
        ((740945 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word22Step31 :
    word22Chunk31.foldl (fun acc a => a.applyPacked acc)
      word22State31 = word22State32 := by decide +kernel

private def word22Chunk32 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word22State33 : PackedMat2 :=
    ⟨⟨⟨((12695537 : Dyadic) * half ^ 25),
        ((852243 : Dyadic) * half ^ 22)⟩,
       ⟨((2097343 : Dyadic) * half ^ 25),
        ((-176581 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((7437537 : Dyadic) * half ^ 25),
        ((-10885809 : Dyadic) * half ^ 25)⟩,
       ⟨((19843 : Dyadic) * half ^ 25),
        ((16719331 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((19843 : Dyadic) * half ^ 25),
        ((16719331 : Dyadic) * half ^ 25)⟩,
       ⟨((7437537 : Dyadic) * half ^ 25),
        ((-10885809 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-2097343 : Dyadic) * half ^ 25),
        ((176581 : Dyadic) * half ^ 21)⟩,
       ⟨((-12695537 : Dyadic) * half ^ 25),
        ((-852243 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word22Step32 :
    word22Chunk32.foldl (fun acc a => a.applyPacked acc)
      word22State32 = word22State33 := by decide +kernel

private def word22Chunk33 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word22State34 : PackedMat2 :=
    ⟨⟨⟨((8218865 : Dyadic) * half ^ 24),
        ((20059241 : Dyadic) * half ^ 26)⟩,
       ⟨((-205703 : Dyadic) * half ^ 23),
        ((7779059 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-8117847 : Dyadic) * half ^ 24),
        ((10388635 : Dyadic) * half ^ 26)⟩,
       ⟨((-11487759 : Dyadic) * half ^ 25),
        ((806621 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((11487759 : Dyadic) * half ^ 25),
        ((-806621 : Dyadic) * half ^ 22)⟩,
       ⟨((8117847 : Dyadic) * half ^ 24),
        ((-10388635 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-205703 : Dyadic) * half ^ 23),
        ((7779059 : Dyadic) * half ^ 25)⟩,
       ⟨((8218865 : Dyadic) * half ^ 24),
        ((20059241 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word22Step33 :
    word22Chunk33.foldl (fun acc a => a.applyPacked acc)
      word22State33 = word22State34 := by decide +kernel

private def word22Chunk34 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word22State35 : PackedMat2 :=
    ⟨⟨⟨((65058677 : Dyadic) * half ^ 27),
        ((-10406111 : Dyadic) * half ^ 27)⟩,
       ⟨((61474395 : Dyadic) * half ^ 27),
        ((6832841 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((8135429 : Dyadic) * half ^ 27),
        ((-30496121 : Dyadic) * half ^ 26)⟩,
       ⟨((-11160639 : Dyadic) * half ^ 27),
        ((-29847425 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-90839667 : Dyadic) * half ^ 27),
        ((-1512605 : Dyadic) * half ^ 27)⟩,
       ⟨((-31144817 : Dyadic) * half ^ 27),
        ((4824017 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-3259571 : Dyadic) * half ^ 27),
        ((-7908317 : Dyadic) * half ^ 24)⟩,
       ⟨((24071793 : Dyadic) * half ^ 27),
        ((-1792141 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word22Step34 :
    word22Chunk34.foldl (fun acc a => a.applyPacked acc)
      word22State34 = word22State35 := by decide +kernel

private def word22Chunk35 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word22State36 : PackedMat2 :=
    ⟨⟨⟨((-18537797 : Dyadic) * half ^ 26),
        ((-9599247 : Dyadic) * half ^ 28)⟩,
       ⟨((12943835 : Dyadic) * half ^ 25),
        ((80915709 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-87941261 : Dyadic) * half ^ 27),
        ((48388965 : Dyadic) * half ^ 28)⟩,
       ⟨((4957487 : Dyadic) * half ^ 27),
        ((-58487199 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((87941261 : Dyadic) * half ^ 27),
        ((-48388965 : Dyadic) * half ^ 28)⟩,
       ⟨((4957487 : Dyadic) * half ^ 27),
        ((-58487199 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-18537797 : Dyadic) * half ^ 26),
        ((-9599247 : Dyadic) * half ^ 28)⟩,
       ⟨((-12943835 : Dyadic) * half ^ 25),
        ((-80915709 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word22Step35 :
    word22Chunk35.foldl (fun acc a => a.applyPacked acc)
      word22State35 = word22State36 := by decide +kernel

private def word22Chunk36 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word22State37 : PackedMat2 :=
    ⟨⟨⟨((-8302963 : Dyadic) * half ^ 25),
        ((-238050671 : Dyadic) * half ^ 29)⟩,
       ⟨((97278197 : Dyadic) * half ^ 28),
        ((1052685 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((7773247 : Dyadic) * half ^ 28),
        ((-132095069 : Dyadic) * half ^ 29)⟩,
       ⟨((-50585491 : Dyadic) * half ^ 27),
        ((147154873 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((50585491 : Dyadic) * half ^ 27),
        ((-147154873 : Dyadic) * half ^ 29)⟩,
       ⟨((-7773247 : Dyadic) * half ^ 28),
        ((132095069 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((97278197 : Dyadic) * half ^ 28),
        ((1052685 : Dyadic) * half ^ 29)⟩,
       ⟨((-8302963 : Dyadic) * half ^ 25),
        ((-238050671 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word22Step36 :
    word22Chunk36.foldl (fun acc a => a.applyPacked acc)
      word22State36 = word22State37 := by decide +kernel

private def word22Chunk37 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word22State38 : PackedMat2 :=
    ⟨⟨⟨((-157936073 : Dyadic) * half ^ 29),
        ((41673455 : Dyadic) * half ^ 28)⟩,
       ⟨((-142575923 : Dyadic) * half ^ 29),
        ((-79298273 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-164726229 : Dyadic) * half ^ 29),
        ((62369459 : Dyadic) * half ^ 29)⟩,
       ⟨((-3077547 : Dyadic) * half ^ 29),
        ((-268174789 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-102902665 : Dyadic) * half ^ 28),
        ((-1310967 : Dyadic) * half ^ 23)⟩,
       ⟨((41318031 : Dyadic) * half ^ 26),
        ((-80824341 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((18812409 : Dyadic) * half ^ 27),
        ((75127999 : Dyadic) * half ^ 28)⟩,
       ⟨((-7560733 : Dyadic) * half ^ 24),
        ((7680075 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word22Step37 :
    word22Chunk37.foldl (fun acc a => a.applyPacked acc)
      word22State37 = word22State38 := by decide +kernel

private def word22Chunk38 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word22State39 : PackedMat2 :=
    ⟨⟨⟨((103464413 : Dyadic) * half ^ 30),
        ((-83241415 : Dyadic) * half ^ 30)⟩,
       ⟨((-144584917 : Dyadic) * half ^ 30),
        ((-70026677 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((203066101 : Dyadic) * half ^ 30),
        ((126852279 : Dyadic) * half ^ 29)⟩,
       ⟨((-943019263 : Dyadic) * half ^ 30),
        ((66971987 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-203066101 : Dyadic) * half ^ 30),
        ((-126852279 : Dyadic) * half ^ 29)⟩,
       ⟨((-943019263 : Dyadic) * half ^ 30),
        ((66971987 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((103464413 : Dyadic) * half ^ 30),
        ((-83241415 : Dyadic) * half ^ 30)⟩,
       ⟨((144584917 : Dyadic) * half ^ 30),
        ((70026677 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word22Step38 :
    word22Chunk38.foldl (fun acc a => a.applyPacked acc)
      word22State38 = word22State39 := by decide +kernel

private def word22Chunk39 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word22State40 : PackedMat2 :=
    ⟨⟨⟨((-112482007 : Dyadic) * half ^ 30),
        ((-10186791 : Dyadic) * half ^ 31)⟩,
       ⟨((-559830779 : Dyadic) * half ^ 30),
        ((-160854345 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((194236599 : Dyadic) * half ^ 28),
        ((52852699 : Dyadic) * half ^ 31)⟩,
       ⟨((30099687 : Dyadic) * half ^ 27),
        ((-549261351 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((301057025 : Dyadic) * half ^ 30),
        ((134037225 : Dyadic) * half ^ 29)⟩,
       ⟨((124102163 : Dyadic) * half ^ 29),
        ((-254435973 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-75333777 : Dyadic) * half ^ 30),
        ((-111837193 : Dyadic) * half ^ 29)⟩,
       ⟨((-10690071 : Dyadic) * half ^ 27),
        ((-336156393 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word22Step39 :
    word22Chunk39.foldl (fun acc a => a.applyPacked acc)
      word22State39 = word22State40 := by decide +kernel

private def word22Chunk40 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word22State41 : PackedMat2 :=
    ⟨⟨⟨((850701013 : Dyadic) * half ^ 31),
        ((472039231 : Dyadic) * half ^ 32)⟩,
       ⟨((-12566013 : Dyadic) * half ^ 30),
        ((-2147592241 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-131639287 : Dyadic) * half ^ 30),
        ((1655805371 : Dyadic) * half ^ 32)⟩,
       ⟨((142164477 : Dyadic) * half ^ 31),
        ((-137865095 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((142164477 : Dyadic) * half ^ 31),
        ((-137865095 : Dyadic) * half ^ 32)⟩,
       ⟨((-131639287 : Dyadic) * half ^ 30),
        ((1655805371 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((12566013 : Dyadic) * half ^ 30),
        ((2147592241 : Dyadic) * half ^ 32)⟩,
       ⟨((-850701013 : Dyadic) * half ^ 31),
        ((-472039231 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word22Step40 :
    word22Chunk40.foldl (fun acc a => a.applyPacked acc)
      word22State40 = word22State41 := by decide +kernel

private def word22Chunk41 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word22State42 : PackedMat2 :=
    ⟨⟨⟨((1243216887 : Dyadic) * half ^ 32),
        ((151891997 : Dyadic) * half ^ 29)⟩,
       ⟨((934891767 : Dyadic) * half ^ 32),
        ((94992419 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((1855725835 : Dyadic) * half ^ 32),
        ((-1374476157 : Dyadic) * half ^ 32)⟩,
       ⟨((-956288649 : Dyadic) * half ^ 32),
        ((398361665 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((244028623 : Dyadic) * half ^ 30),
        ((-449718593 : Dyadic) * half ^ 32)⟩,
       ⟨((886418911 : Dyadic) * half ^ 31),
        ((-703003621 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((341876835 : Dyadic) * half ^ 29),
        ((1089054327 : Dyadic) * half ^ 32)⟩,
       ⟨((-38092841 : Dyadic) * half ^ 29),
        ((1204395 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word22Step41 :
    word22Chunk41.foldl (fun acc a => a.applyPacked acc)
      word22State41 = word22State42 := by decide +kernel

private def word22Chunk42 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word22State43 : PackedMat2 :=
    ⟨⟨⟨((2471494677 : Dyadic) * half ^ 33),
        ((-363190205 : Dyadic) * half ^ 32)⟩,
       ⟨((6055812117 : Dyadic) * half ^ 33),
        ((744020501 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((942351015 : Dyadic) * half ^ 33),
        ((2546418497 : Dyadic) * half ^ 33)⟩,
       ⟨((2347706437 : Dyadic) * half ^ 33),
        ((-1088301123 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((942351015 : Dyadic) * half ^ 33),
        ((2546418497 : Dyadic) * half ^ 33)⟩,
       ⟨((-2347706437 : Dyadic) * half ^ 33),
        ((1088301123 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-2471494677 : Dyadic) * half ^ 33),
        ((363190205 : Dyadic) * half ^ 32)⟩,
       ⟨((6055812117 : Dyadic) * half ^ 33),
        ((744020501 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word22Step42 :
    word22Chunk42.foldl (fun acc a => a.applyPacked acc)
      word22State42 = word22State43 := by decide +kernel

private def word22Chunk43 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word22State44 : PackedMat2 :=
    ⟨⟨⟨((-2637343481 : Dyadic) * half ^ 33),
        ((-1256238261 : Dyadic) * half ^ 33)⟩,
       ⟨((-123015425 : Dyadic) * half ^ 29),
        ((71763985 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((1451682101 : Dyadic) * half ^ 33),
        ((359832379 : Dyadic) * half ^ 33)⟩,
       ⟨((-127237385 : Dyadic) * half ^ 31),
        ((5315851433 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2478009527 : Dyadic) * half ^ 32),
        ((-1960631641 : Dyadic) * half ^ 34)⟩,
       ⟨((1418920953 : Dyadic) * half ^ 31),
        ((942732561 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1830350141 : Dyadic) * half ^ 33),
        ((-669096681 : Dyadic) * half ^ 34)⟩,
       ⟨((682126381 : Dyadic) * half ^ 33),
        ((4605590281 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word22Step43 :
    word22Chunk43.foldl (fun acc a => a.applyPacked acc)
      word22State43 = word22State44 := by decide +kernel

private def word22Chunk44 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word22State45 : PackedMat2 :=
    ⟨⟨⟨((-687531097 : Dyadic) * half ^ 31),
        ((-4462279081 : Dyadic) * half ^ 35)⟩,
       ⟨((-7164803533 : Dyadic) * half ^ 34),
        ((-7391702683 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((3058964439 : Dyadic) * half ^ 34),
        ((-7059241983 : Dyadic) * half ^ 35)⟩,
       ⟨((5700629293 : Dyadic) * half ^ 33),
        ((-4903824603 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-5700629293 : Dyadic) * half ^ 33),
        ((4903824603 : Dyadic) * half ^ 35)⟩,
       ⟨((-3058964439 : Dyadic) * half ^ 34),
        ((7059241983 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-7164803533 : Dyadic) * half ^ 34),
        ((-7391702683 : Dyadic) * half ^ 35)⟩,
       ⟨((-687531097 : Dyadic) * half ^ 31),
        ((-4462279081 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word22Step44 :
    word22Chunk44.foldl (fun acc a => a.applyPacked acc)
      word22State44 = word22State45 := by decide +kernel

private def word22Chunk45 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word22State46 : PackedMat2 :=
    ⟨⟨⟨((-2717337683 : Dyadic) * half ^ 32),
        ((8122893003 : Dyadic) * half ^ 36)⟩,
       ⟨((-10900580569 : Dyadic) * half ^ 35),
        ((-5325443887 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((3916082443 : Dyadic) * half ^ 35),
        ((-20738957587 : Dyadic) * half ^ 36)⟩,
       ⟨((-7443550095 : Dyadic) * half ^ 34),
        ((-13417400367 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((1830389305 : Dyadic) * half ^ 34),
        ((-18803182633 : Dyadic) * half ^ 36)⟩,
       ⟨((-17078178977 : Dyadic) * half ^ 35),
        ((-10971017747 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((6724168445 : Dyadic) * half ^ 35),
        ((-10838120895 : Dyadic) * half ^ 36)⟩,
       ⟨((-699362279 : Dyadic) * half ^ 34),
        ((32639282033 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word22Step45 :
    word22Chunk45.foldl (fun acc a => a.applyPacked acc)
      word22State45 = word22State46 := by decide +kernel

private def word22Chunk46 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word22State47 : PackedMat2 :=
    ⟨⟨⟨((2068186691 : Dyadic) * half ^ 35),
        ((-3223084963 : Dyadic) * half ^ 33)⟩,
       ⟨((-5787015727 : Dyadic) * half ^ 34),
        ((-17208612861 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((1262180793 : Dyadic) * half ^ 34),
        ((6643752285 : Dyadic) * half ^ 35)⟩,
       ⟨((3059345885 : Dyadic) * half ^ 34),
        ((-29318025485 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-3059345885 : Dyadic) * half ^ 34),
        ((29318025485 : Dyadic) * half ^ 36)⟩,
       ⟨((-1262180793 : Dyadic) * half ^ 34),
        ((-6643752285 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-5787015727 : Dyadic) * half ^ 34),
        ((-17208612861 : Dyadic) * half ^ 36)⟩,
       ⟨((2068186691 : Dyadic) * half ^ 35),
        ((-3223084963 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word22Step46 :
    word22Chunk46.foldl (fun acc a => a.applyPacked acc)
      word22State46 = word22State47 := by decide +kernel

private def word22Chunk47 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word22State48 : PackedMat2 :=
    ⟨⟨⟨((-10660133103 : Dyadic) * half ^ 37),
        ((-1198601759 : Dyadic) * half ^ 35)⟩,
       ⟨((-22673006223 : Dyadic) * half ^ 37),
        ((-27317485225 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-27355554665 : Dyadic) * half ^ 37),
        ((77033263115 : Dyadic) * half ^ 37)⟩,
       ⟨((-48467486251 : Dyadic) * half ^ 37),
        ((-3705600449 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-27355554665 : Dyadic) * half ^ 37),
        ((77033263115 : Dyadic) * half ^ 37)⟩,
       ⟨((48467486251 : Dyadic) * half ^ 37),
        ((3705600449 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((10660133103 : Dyadic) * half ^ 37),
        ((1198601759 : Dyadic) * half ^ 35)⟩,
       ⟨((-22673006223 : Dyadic) * half ^ 37),
        ((-27317485225 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word22Step47 :
    word22Chunk47.foldl (fun acc a => a.applyPacked acc)
      word22State47 = word22State48 := by decide +kernel

private def word22Chunk48 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word22State49 : PackedMat2 :=
    ⟨⟨⟨((145628603993 : Dyadic) * half ^ 38),
        ((-46401679 : Dyadic) * half ^ 32)⟩,
       ⟨((163433547161 : Dyadic) * half ^ 38),
        ((-5496126489 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((22633145871 : Dyadic) * half ^ 38),
        ((58663070007 : Dyadic) * half ^ 38)⟩,
       ⟨((-29835755 : Dyadic) * half ^ 38),
        ((-12551962061 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((41752626481 : Dyadic) * half ^ 38),
        ((-5650827529 : Dyadic) * half ^ 37)⟩,
       ⟨((-159078766495 : Dyadic) * half ^ 38),
        ((-11331490813 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-8465833945 : Dyadic) * half ^ 38),
        ((154531075577 : Dyadic) * half ^ 38)⟩,
       ⟨((2526419033 : Dyadic) * half ^ 38),
        ((-278202237 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word22Step48 :
    word22Chunk48.foldl (fun acc a => a.applyPacked acc)
      word22State48 = word22State49 := by decide +kernel

private def word22Chunk49 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word22State50 : PackedMat2 :=
    ⟨⟨⟨((10493948447 : Dyadic) * half ^ 34),
        ((-87506222213 : Dyadic) * half ^ 39)⟩,
       ⟨((103871214215 : Dyadic) * half ^ 38),
        ((74715443357 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-41884625337 : Dyadic) * half ^ 38),
        ((59233593989 : Dyadic) * half ^ 39)⟩,
       ⟨((78504160989 : Dyadic) * half ^ 37),
        ((59950743413 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-78504160989 : Dyadic) * half ^ 37),
        ((-59950743413 : Dyadic) * half ^ 39)⟩,
       ⟨((41884625337 : Dyadic) * half ^ 38),
        ((-59233593989 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((103871214215 : Dyadic) * half ^ 38),
        ((74715443357 : Dyadic) * half ^ 39)⟩,
       ⟨((10493948447 : Dyadic) * half ^ 34),
        ((-87506222213 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word22Step49 :
    word22Chunk49.foldl (fun acc a => a.applyPacked acc)
      word22State49 = word22State50 := by decide +kernel

private def word22Chunk50 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word22State51 : PackedMat2 :=
    ⟨⟨⟨((-17184557225 : Dyadic) * half ^ 38),
        ((40130206295 : Dyadic) * half ^ 37)⟩,
       ⟨((50183498293 : Dyadic) * half ^ 37),
        ((89734900103 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-50411485551 : Dyadic) * half ^ 37),
        ((-54608859361 : Dyadic) * half ^ 38)⟩,
       ⟨((-37459264269 : Dyadic) * half ^ 37),
        ((230378230079 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((121160511357 : Dyadic) * half ^ 39),
        ((-21967687455 : Dyadic) * half ^ 36)⟩,
       ⟨((-339595948801 : Dyadic) * half ^ 39),
        ((-6476110641 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-250255725283 : Dyadic) * half ^ 39),
        ((-83182439361 : Dyadic) * half ^ 39)⟩,
       ⟨((-70785925077 : Dyadic) * half ^ 39),
        ((117551553811 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word22Step50 :
    word22Chunk50.foldl (fun acc a => a.applyPacked acc)
      word22State50 = word22State51 := by decide +kernel

private def word22Chunk51 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word22State52 : PackedMat2 :=
    ⟨⟨⟨((-297224895849 : Dyadic) * half ^ 40),
        ((-59628124727 : Dyadic) * half ^ 37)⟩,
       ⟨((164989674737 : Dyadic) * half ^ 40),
        ((-76409865641 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((46256164929 : Dyadic) * half ^ 40),
        ((-307585779101 : Dyadic) * half ^ 40)⟩,
       ⟨((270085619401 : Dyadic) * half ^ 40),
        ((-212801274169 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((733188327439 : Dyadic) * half ^ 40),
        ((-158170892165 : Dyadic) * half ^ 40)⟩,
       ⟨((-118016769237 : Dyadic) * half ^ 40),
        ((27978681809 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-553434863457 : Dyadic) * half ^ 40),
        ((-16529402639 : Dyadic) * half ^ 38)⟩,
       ⟨((-400615132175 : Dyadic) * half ^ 40),
        ((-231107285293 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word22Step51 :
    word22Chunk51.foldl (fun acc a => a.applyPacked acc)
      word22State51 = word22State52 := by decide +kernel

private def word22Chunk52 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word22State53 : PackedMat2 :=
    ⟨⟨⟨((-106119256371 : Dyadic) * half ^ 38),
        ((-323208789273 : Dyadic) * half ^ 40)⟩,
       ⟨((-201894231101 : Dyadic) * half ^ 40),
        ((-154905275545 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-262561713085 : Dyadic) * half ^ 39),
        ((137067144727 : Dyadic) * half ^ 39)⟩,
       ⟨((-253862017949 : Dyadic) * half ^ 40),
        ((109881209529 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-262561713085 : Dyadic) * half ^ 39),
        ((137067144727 : Dyadic) * half ^ 39)⟩,
       ⟨((253862017949 : Dyadic) * half ^ 40),
        ((-109881209529 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((106119256371 : Dyadic) * half ^ 38),
        ((323208789273 : Dyadic) * half ^ 40)⟩,
       ⟨((-201894231101 : Dyadic) * half ^ 40),
        ((-154905275545 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word22Step52 :
    word22Chunk52.foldl (fun acc a => a.applyPacked acc)
      word22State52 = word22State53 := by decide +kernel

private def word22Chunk53 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word22State54 : PackedMat2 :=
    ⟨⟨⟨((-938420055957 : Dyadic) * half ^ 41),
        ((549652495331 : Dyadic) * half ^ 42)⟩,
       ⟨((-274617499515 : Dyadic) * half ^ 39),
        ((-778944632527 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((84555628247 : Dyadic) * half ^ 40),
        ((-2116142947041 : Dyadic) * half ^ 42)⟩,
       ⟨((-98996826237 : Dyadic) * half ^ 41),
        ((-182038251373 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((483526173917 : Dyadic) * half ^ 40),
        ((-268108082731 : Dyadic) * half ^ 42)⟩,
       ⟨((-1149090599207 : Dyadic) * half ^ 41),
        ((70114430257 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((664298563929 : Dyadic) * half ^ 41),
        ((160049942103 : Dyadic) * half ^ 42)⟩,
       ⟨((57323034299 : Dyadic) * half ^ 40),
        ((2036890054017 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word22Step53 :
    word22Chunk53.foldl (fun acc a => a.applyPacked acc)
      word22State53 = word22State54 := by decide +kernel

private def word22Chunk54 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word22State55 : PackedMat2 :=
    ⟨⟨⟨((917060241445 : Dyadic) * half ^ 40),
        ((15154249571 : Dyadic) * half ^ 40)⟩,
       ⟨((-551843362851 : Dyadic) * half ^ 41),
        ((-319089247951 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-186434107081 : Dyadic) * half ^ 41),
        ((170396201453 : Dyadic) * half ^ 39)⟩,
       ⟨((-383168223939 : Dyadic) * half ^ 41),
        ((86449894303 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((383168223939 : Dyadic) * half ^ 41),
        ((-86449894303 : Dyadic) * half ^ 42)⟩,
       ⟨((186434107081 : Dyadic) * half ^ 41),
        ((-170396201453 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-551843362851 : Dyadic) * half ^ 41),
        ((-319089247951 : Dyadic) * half ^ 42)⟩,
       ⟨((917060241445 : Dyadic) * half ^ 40),
        ((15154249571 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word22Step54 :
    word22Chunk54.foldl (fun acc a => a.applyPacked acc)
      word22State54 = word22State55 := by decide +kernel

private def word22Chunk55 : List Letter := [.s, .t, .h, .t, .h, .s]
private def word22State56 : PackedMat2 :=
    ⟨⟨⟨((1565975791455 : Dyadic) * half ^ 41),
        ((895264309351 : Dyadic) * half ^ 42)⟩,
       ⟨((143714478057 : Dyadic) * half ^ 42),
        ((-101623811339 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((14659256781 : Dyadic) * half ^ 41),
        ((-10365659877 : Dyadic) * half ^ 41)⟩,
       ⟨((1985908888797 : Dyadic) * half ^ 42),
        ((-1404249642087 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-14659256781 : Dyadic) * half ^ 41),
        ((10365659877 : Dyadic) * half ^ 41)⟩,
       ⟨((1985908888797 : Dyadic) * half ^ 42),
        ((-1404249642087 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1565975791455 : Dyadic) * half ^ 41),
        ((895264309351 : Dyadic) * half ^ 42)⟩,
       ⟨((-143714478057 : Dyadic) * half ^ 42),
        ((101623811339 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word22Step55 :
    word22Chunk55.foldl (fun acc a => a.applyPacked acc)
      word22State55 = word22State56 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word22_check : check word22 22 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word22 = word22State56.toMatrix := by
    unfold evalRingPacked
    change ((
      word22Chunk0 ++ word22Chunk1 ++ word22Chunk2 ++ word22Chunk3 ++
      word22Chunk4 ++ word22Chunk5 ++ word22Chunk6 ++ word22Chunk7 ++
      word22Chunk8 ++ word22Chunk9 ++ word22Chunk10 ++ word22Chunk11 ++
      word22Chunk12 ++ word22Chunk13 ++ word22Chunk14 ++ word22Chunk15 ++
      word22Chunk16 ++ word22Chunk17 ++ word22Chunk18 ++ word22Chunk19 ++
      word22Chunk20 ++ word22Chunk21 ++ word22Chunk22 ++ word22Chunk23 ++
      word22Chunk24 ++ word22Chunk25 ++ word22Chunk26 ++ word22Chunk27 ++
      word22Chunk28 ++ word22Chunk29 ++ word22Chunk30 ++ word22Chunk31 ++
      word22Chunk32 ++ word22Chunk33 ++ word22Chunk34 ++ word22Chunk35 ++
      word22Chunk36 ++ word22Chunk37 ++ word22Chunk38 ++ word22Chunk39 ++
      word22Chunk40 ++ word22Chunk41 ++ word22Chunk42 ++ word22Chunk43 ++
      word22Chunk44 ++ word22Chunk45 ++ word22Chunk46 ++ word22Chunk47 ++
      word22Chunk48 ++ word22Chunk49 ++ word22Chunk50 ++ word22Chunk51 ++
      word22Chunk52 ++ word22Chunk53 ++ word22Chunk54 ++ word22Chunk55
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word22Step0, word22Step1, word22Step2, word22Step3, word22Step4,
      word22Step5, word22Step6, word22Step7, word22Step8, word22Step9,
      word22Step10, word22Step11, word22Step12, word22Step13, word22Step14,
      word22Step15, word22Step16, word22Step17, word22Step18, word22Step19,
      word22Step20, word22Step21, word22Step22, word22Step23, word22Step24,
      word22Step25, word22Step26, word22Step27, word22Step28, word22Step29,
      word22Step30, word22Step31, word22Step32, word22Step33, word22Step34,
      word22Step35, word22Step36, word22Step37, word22Step38, word22Step39,
      word22Step40, word22Step41, word22Step42, word22Step43, word22Step44,
      word22Step45, word22Step46, word22Step47, word22Step48, word22Step49,
      word22Step50, word22Step51, word22Step52, word22Step53, word22Step54,
      word22Step55]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
