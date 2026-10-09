import Lean
import Mathlib

namespace GapCVP.BinaryEncoding
end GapCVP.BinaryEncoding
namespace GapCVP.Factor400BinaryCodeDecodingCorollary
end GapCVP.Factor400BinaryCodeDecodingCorollary
section

noncomputable section

open StateTransition (EvalsToInTime)

namespace GapCVP

section

abbrev Literal := ℕ × Bool

abbrev ThreeClause := Fin 3 → Literal

abbrev ThreeCNF := List ThreeClause

structure GapCVPInstance where
  dimension : ℕ
  basis : Matrix (Fin dimension) (Fin dimension) ℤ
  target : Fin dimension → ℚ
  radius : ℚ

namespace BinaryEncoding

def lengthPrefixedWord (word : List Bool) : List Bool :=
  List.replicate word.length true ++ false :: word

def readUnaryPrefix : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
      match readUnaryPrefix rest with
      | none => none
      | some (n, tail) => some (n + 1, tail)

@[simp] theorem readUnaryPrefix_replicate
    (n : ℕ) (tail : List Bool) :
    readUnaryPrefix (List.replicate n true ++ false :: tail) =
      some (n, tail) := by
  induction n with
  | zero => simp [readUnaryPrefix]
  | succ n ih =>
      simp [List.replicate_succ, readUnaryPrefix, ih]

def readLengthPrefixedWord (bits : List Bool) :
    Option (List Bool × List Bool) :=
  match readUnaryPrefix bits with
  | none => none
  | some (n, tail) =>
      if n ≤ tail.length then
        some (tail.take n, tail.drop n)
      else
        none

@[simp] theorem readLengthPrefixedWord_append
    (word suffix : List Bool) :
    readLengthPrefixedWord (lengthPrefixedWord word ++ suffix) =
      some (word, suffix) := by
  simp [lengthPrefixedWord, readLengthPrefixedWord,
    List.append_assoc, readUnaryPrefix_replicate]

def readLiteral (bits : List Bool) : Option (Literal × List Bool) :=
  match readLengthPrefixedWord bits with
  | some (word, sign :: rest) =>
      some ((Computability.decodeNat word, sign), rest)
  | _ => none

def readThreeClause (bits : List Bool) :
    Option (ThreeClause × List Bool) :=
  match readLiteral bits with
  | some (a, rest₁) =>
      match readLiteral rest₁ with
      | some (b, rest₂) =>
          match readLiteral rest₂ with
          | some (c, rest₃) => some (![a, b, c], rest₃)
          | none => none
      | none => none
  | none => none

def readThreeClauses : ℕ → List Bool → Option (ThreeCNF × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits =>
      match readThreeClause bits with
      | none => none
      | some (clause, rest) =>
          match readThreeClauses n rest with
          | none => none
          | some (clauses, suffix) => some (clause :: clauses, suffix)

def decodeThreeCNF (bits : List Bool) : Option ThreeCNF :=
  match readLengthPrefixedWord bits with
  | none => none
  | some (word, rest) =>
      match readThreeClauses (Computability.decodeNat word) rest with
      | some (clauses, []) => some clauses
      | _ => none

end BinaryEncoding

end

namespace BinaryEncoding

def encodeAtomic {α : Type*} [Encodable α] (a : α) : List Bool :=
  lengthPrefixedWord (Computability.encodeNat (Encodable.encode a))

def readAtomic {α : Type*} [Encodable α] (bits : List Bool) :
    Option (α × List Bool) :=
  match readLengthPrefixedWord bits with
  | none => none
  | some (word, suffix) =>
      match (Encodable.decode (Computability.decodeNat word) : Option α) with
      | none => none
      | some a => some (a, suffix)

@[simp] theorem readAtomic_append
    {α : Type*} [Encodable α] (a : α) (suffix : List Bool) :
    readAtomic (encodeAtomic a ++ suffix) = some (a, suffix) := by
  simp [readAtomic, encodeAtomic]

def encodeFinValues {α : Type*} [Encodable α] :
    (n : ℕ) → (Fin n → α) → List Bool
  | 0, _ => []
  | n + 1, values =>
      encodeAtomic (values 0) ++
        encodeFinValues n (fun i => values i.succ)

def readFinValues {α : Type*} [Encodable α] :
    (n : ℕ) → List Bool → Option ((Fin n → α) × List Bool)
  | 0, bits => some (Fin.elim0, bits)
  | n + 1, bits =>
      match (readAtomic bits : Option (α × List Bool)) with
      | none => none
      | some (head, rest) =>
          match readFinValues n rest with
          | none => none
          | some (tail, suffix) => some (Fin.cases head tail, suffix)

@[simp] theorem readFinValues_append
    {α : Type*} [Encodable α]
    {n : ℕ} (values : Fin n → α) (suffix : List Bool) :
    readFinValues n (encodeFinValues n values ++ suffix) =
      some (values, suffix) := by
  induction n with
  | zero =>
      have hvalues : values = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp [encodeFinValues, readFinValues, hvalues]
  | succ n ih =>
      have hvalues :
          Fin.cases (values 0) (fun i : Fin n => values i.succ) =
            values := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      simp [encodeFinValues, readFinValues, List.append_assoc,
        ih, hvalues]

def encodeMatrixRows :
    (m n : ℕ) → (Fin m → Fin n → ℤ) → List Bool
  | 0, _, _ => []
  | m + 1, n, matrix =>
      encodeFinValues n (matrix 0) ++
        encodeMatrixRows m n (fun i => matrix i.succ)

def readMatrixRows :
    (m n : ℕ) → List Bool →
      Option ((Fin m → Fin n → ℤ) × List Bool)
  | 0, _, bits => some (Fin.elim0, bits)
  | m + 1, n, bits =>
      match (readFinValues n bits :
        Option ((Fin n → ℤ) × List Bool)) with
      | none => none
      | some (row, rest) =>
          match readMatrixRows m n rest with
          | none => none
          | some (rows, suffix) => some (Fin.cases row rows, suffix)

@[simp] theorem readMatrixRows_append
    {m n : ℕ} (matrix : Fin m → Fin n → ℤ)
    (suffix : List Bool) :
    readMatrixRows m n (encodeMatrixRows m n matrix ++ suffix) =
      some (matrix, suffix) := by
  induction m with
  | zero =>
      have hmatrix : matrix = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp [encodeMatrixRows, readMatrixRows, hmatrix]
  | succ m ih =>
      have hmatrix :
          Fin.cases (matrix 0) (fun i : Fin m => matrix i.succ) =
            matrix := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      simp [encodeMatrixRows, readMatrixRows, List.append_assoc,
        ih, hmatrix]

def decodeGapCVPInstance (bits : List Bool) : Option GapCVPInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (n, afterDimension) =>
      match (readAtomic afterDimension : Option (ℚ × List Bool)) with
      | none => none
      | some (radius, afterRadius) =>
          match (readFinValues n afterRadius :
            Option ((Fin n → ℚ) × List Bool)) with
          | none => none
          | some (target, afterTarget) =>
              match readMatrixRows n n afterTarget with
              | some (basis, []) =>
                  some {
                    dimension := n
                    basis := basis
                    target := target
                    radius := radius
                  }
              | _ => none

end BinaryEncoding

section

open Computability

abbrev BitLanguage := List Bool → Bool

abbrev bitEncoding : List Bool → List Bool := id

def pairBitEncoding : (List Bool × List Bool) →
    List (Bool ⊕ Bool) :=
  (Computability.encodingProd
    (Computability.encodingList Bool)
    (Computability.encodingList Bool)).encode

abbrev BitTM (f : List Bool → List Bool) :=
  Turing.TM2ComputableInPolyTime bitEncoding bitEncoding f

abbrev VerifierTM (verifier : List Bool × List Bool → Bool) :=
  Turing.TM2ComputableInPolyTime
    pairBitEncoding Computability.encodeBool verifier

noncomputable def IsNP (L : BitLanguage) : Bool :=
  @decide (
  ∃ (bound : Polynomial ℕ) (verifier : List Bool × List Bool → Bool),
    Nonempty (VerifierTM verifier) ∧
      ∀ x : List Bool,
        L x ↔ ∃ certificate : List Bool,
          certificate.length ≤ bound.eval x.length ∧
            verifier (x, certificate) = true
  ) (Classical.propDecidable _)

end

section

noncomputable def gapFactor400 (I : GapCVPInstance) : ℝ :=
  (I.dimension : ℝ) ^ ((1 : ℝ) / 400)

end

namespace Factor400FinitePNormCorollary

open scoped BigOperators ENNReal

def finitePGapFactor (p : ℚ) (I : GapCVPInstance) : ℝ :=
  (I.dimension : ℝ) ^ (((200 : ℝ) * (p : ℝ))⁻¹)

end Factor400FinitePNormCorollary

namespace Factor400BinaryDecodingPromiseReduction

open scoped BigOperators

open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.BinaryEncoding

structure BinaryNearestCodewordInstance where
  blockLength : ℕ
  generatorRank : ℕ
  generator : Fin blockLength → Fin generatorRank → ZMod 2
  target : Fin blockLength → ZMod 2
  radius : ℕ

def binaryVectorOfIntegers {n : ℕ} (values : Fin n → ℤ) :
    Option (Fin n → ZMod 2) :=
  if ∀ index, values index = 0 ∨ values index = 1 then
    some (fun index => (values index : ZMod 2))
  else
    none

def binaryMatrixOfIntegers {m n : ℕ}
    (values : Fin m → Fin n → ℤ) :
    Option (Fin m → Fin n → ZMod 2) :=
  if ∀ row column, values row column = 0 ∨ values row column = 1 then
    some (fun row column => (values row column : ZMod 2))
  else
    none

def decodeBinaryNearestCodewordInstance
    (bits : List Bool) : Option BinaryNearestCodewordInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (blockLength, tail) =>
    match (readAtomic tail : Option (ℕ × List Bool)) with
    | none => none
    | some (generatorRank, tail) =>
      match (readAtomic tail : Option (ℕ × List Bool)) with
      | none => none
      | some (radius, tail) =>
        match (readFinValues blockLength tail :
          Option ((Fin blockLength → ℤ) × List Bool)) with
        | none => none
        | some (target, tail) =>
          match binaryVectorOfIntegers target with
          | none => none
          | some target =>
            match readMatrixRows blockLength generatorRank tail with
            | some (generator, []) =>
              match binaryMatrixOfIntegers generator with
              | some generator =>
                some ⟨blockLength, generatorRank, generator, target, radius⟩
              | none => none
            | _ => none

end Factor400BinaryDecodingPromiseReduction

noncomputable section

open scoped BigOperators

namespace Comparator

structure Instance where
  dimension : ℕ
  basis : Matrix (Fin dimension) (Fin dimension) ℤ
  target : Fin dimension → ℚ
  radius : ℚ

export GapCVP.BinaryEncoding
  (lengthPrefixedWord
   readUnaryPrefix
   readUnaryPrefix_replicate
   readLengthPrefixedWord
   readLengthPrefixedWord_append
   encodeAtomic
   readAtomic
   readAtomic_append
   encodeFinValues
   readFinValues
   readFinValues_append
   encodeMatrixRows
   readMatrixRows
   readMatrixRows_append)

export GapCVP (BitLanguage bitEncoding pairBitEncoding IsNP)

def encodeInstance (I : Instance) : List Bool :=
  encodeAtomic I.dimension ++
    encodeAtomic I.radius ++
    encodeFinValues I.dimension I.target ++
    encodeMatrixRows I.dimension I.dimension I.basis

def decodeInstance (bits : List Bool) : Option Instance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (dimension, afterDimension) =>
      match (readAtomic afterDimension : Option (ℚ × List Bool)) with
      | none => none
      | some (radius, afterRadius) =>
          match (readFinValues dimension afterRadius :
            Option ((Fin dimension → ℚ) × List Bool)) with
          | none => none
          | some (target, afterTarget) =>
              match readMatrixRows dimension dimension afterTarget with
              | some (basis, []) =>
                  some { dimension, basis, target, radius }
              | _ => none

@[simp] theorem decodeInstance_encode (record : Instance) :
    decodeInstance (encodeInstance record) = some record := by
  cases record with
  | mk dimension basis target radius =>
      have matrix :
          readMatrixRows dimension dimension
              (encodeMatrixRows dimension dimension basis) =
            some (basis, []) := by
        change
          readMatrixRows dimension dimension
              (encodeMatrixRows dimension dimension
                (fun row column => basis row column)) =
            some ((fun row column => basis row column), [])
        simpa only [List.append_nil] using
          readMatrixRows_append (fun row column => basis row column) []
      simp [decodeInstance, encodeInstance, List.append_assoc, matrix]

theorem encodeInstance_injective : Function.Injective encodeInstance := by
  intro first second same
  simpa using congrArg decodeInstance same

def wellFormed (record : Instance) : Bool :=
  @decide
    (0 < record.dimension ∧ record.basis.det ≠ 0 ∧ 0 < record.radius)
    (Classical.propDecidable _)

def hasIntegerTarget (record : Instance) : Bool :=
  @decide
    (∀ index : Fin record.dimension,
      ∃ value : ℤ, record.target index = (value : ℚ))
    (Classical.propDecidable _)

noncomputable def distanceSquared (I : Instance)
    (vector : Fin I.dimension → ℤ) : ℝ :=
  ∑ i : Fin I.dimension,
    (((∑ j : Fin I.dimension,
      (I.basis i j : ℝ) * (vector j : ℝ)) -
        (I.target i : ℝ)) ^ 2)

noncomputable def gapFactor400 (I : Instance) : ℝ :=
  (I.dimension : ℝ) ^ ((1 : ℝ) / 400)

def gapYES400 (record : Instance) : Bool :=
  @decide
    (wellFormed record ∧
      ∃ vector : Fin record.dimension → ℤ,
        distanceSquared record vector ≤ (record.radius : ℝ) ^ 2)
    (Classical.propDecidable _)

def gapNO400 (record : Instance) : Bool :=
  @decide
    (wellFormed record ∧
      ∀ vector : Fin record.dimension → ℤ,
        (gapFactor400 record * (record.radius : ℝ)) ^ 2 <
          distanceSquared record vector)
    (Classical.propDecidable _)

theorem gapYES400_not_gapNO400 (record : Instance)
    (positive : gapYES400 record) (negative : gapNO400 record) : False := by
  simp only [gapYES400, gapNO400, wellFormed, decide_eq_true_eq]
    at positive negative
  obtain ⟨⟨dimension, _, radius⟩, vector, close⟩ := positive
  have factor : 1 ≤ gapFactor400 record := by
    unfold gapFactor400
    apply Real.one_le_rpow
    · exact_mod_cast dimension
    · norm_num
  have radiusReal : 0 < (record.radius : ℝ) := by
    exact_mod_cast radius
  have scaled :
      (record.radius : ℝ) ≤
        gapFactor400 record * (record.radius : ℝ) := by
    nlinarith
  have squares :
      (record.radius : ℝ) ^ 2 ≤
        (gapFactor400 record * (record.radius : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (gapFactor400 record * (record.radius : ℝ)),
      sq_nonneg (record.radius : ℝ)]
  linarith [negative.2 vector]

def yesLanguage (bits : List Bool) : Bool :=
  @decide
    (∃ record : Instance,
      encodeInstance record = bits ∧
        hasIntegerTarget record ∧ gapYES400 record)
    (Classical.propDecidable _)

def noLanguage (bits : List Bool) : Bool :=
  @decide
    (∃ record : Instance,
      encodeInstance record = bits ∧
        hasIntegerTarget record ∧ gapNO400 record)
    (Classical.propDecidable _)

structure PromiseProblem where
  yes : BitLanguage
  no : BitLanguage
  disjoint : ∀ bits, yes bits → no bits → False

-- Definition hole: project body verbatim; body not checked by Comparator.
def gapCVP400Promise : PromiseProblem where
  yes := yesLanguage
  no := noLanguage
  disjoint bits positive negative := by
    simp only [yesLanguage, noLanguage, decide_eq_true_eq]
      at positive negative
    obtain ⟨first, hfirst, _, hyes⟩ := positive
    obtain ⟨second, hsecond, _, hno⟩ := negative
    have same := encodeInstance_injective (hfirst.trans hsecond.symm)
    subst second
    exact gapYES400_not_gapNO400 first hyes hno

structure BinaryNearestCodewordInstance where
  blockLength : ℕ
  generatorRank : ℕ
  generator : Fin blockLength → Fin generatorRank → ZMod 2
  target : Fin blockLength → ZMod 2
  radius : ℕ

structure BinarySyndromeDecodingInstance where
  checkCount : ℕ
  blockLength : ℕ
  parityCheck : Fin checkCount → Fin blockLength → ZMod 2
  syndrome : Fin checkCount → ZMod 2
  radius : ℕ

def encodeBinaryNearestCodewordInstance
    (record : BinaryNearestCodewordInstance) : List Bool :=
  encodeAtomic record.blockLength ++
    encodeAtomic record.generatorRank ++
    encodeAtomic record.radius ++
    encodeFinValues record.blockLength
      (fun index => ((record.target index).val : ℤ)) ++
    encodeMatrixRows record.blockLength record.generatorRank
      (fun row column => ((record.generator row column).val : ℤ))

def encodeBinarySyndromeDecodingInstance
    (record : BinarySyndromeDecodingInstance) : List Bool :=
  encodeAtomic record.checkCount ++
    encodeAtomic record.blockLength ++
    encodeAtomic record.radius ++
    encodeFinValues record.checkCount
      (fun row => ((record.syndrome row).val : ℤ)) ++
    encodeMatrixRows record.checkCount record.blockLength
      (fun row column => ((record.parityCheck row column).val : ℤ))

@[simp] theorem binaryIntegerRepresentative_cast (value : ZMod 2) :
    (((value.val : ℕ) : ℤ) : ZMod 2) = value := by
  rw [Int.cast_natCast]
  exact ZMod.natCast_zmod_val value

def decodeBinaryNearestCodewordInstance
    (bits : List Bool) : Option BinaryNearestCodewordInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (blockLength, afterBlockLength) =>
      match (readAtomic afterBlockLength : Option (ℕ × List Bool)) with
      | none => none
      | some (generatorRank, afterGeneratorRank) =>
          match (readAtomic afterGeneratorRank : Option (ℕ × List Bool)) with
          | none => none
          | some (radius, afterRadius) =>
              match (readFinValues blockLength afterRadius :
                Option ((Fin blockLength → ℤ) × List Bool)) with
              | none => none
              | some (target, afterTarget) =>
                  match readMatrixRows blockLength generatorRank afterTarget with
                  | some (generator, []) =>
                      some {
                        blockLength
                        generatorRank
                        generator := fun row column =>
                          (generator row column : ZMod 2)
                        target := fun index => (target index : ZMod 2)
                        radius
                      }
                  | _ => none

@[simp] theorem decodeBinaryNearestCodewordInstance_encode
    (record : BinaryNearestCodewordInstance) :
    decodeBinaryNearestCodewordInstance
      (encodeBinaryNearestCodewordInstance record) = some record := by
  cases record with
  | mk blockLength generatorRank generator target radius =>
      have matrix :
          readMatrixRows blockLength generatorRank
              (encodeMatrixRows blockLength generatorRank
                (fun row column => ((generator row column).val : ℤ))) =
            some ((fun row column => ((generator row column).val : ℤ)), []) := by
        simpa using
          readMatrixRows_append
            (fun row column => ((generator row column).val : ℤ)) []
      simp only [decodeBinaryNearestCodewordInstance,
        encodeBinaryNearestCodewordInstance, List.append_assoc,
        readAtomic_append, readFinValues_append, matrix,
        binaryIntegerRepresentative_cast]

theorem encodeBinaryNearestCodewordInstance_injective :
    Function.Injective encodeBinaryNearestCodewordInstance := by
  intro first second same
  simpa using congrArg decodeBinaryNearestCodewordInstance same

def decodeBinarySyndromeDecodingInstance
    (bits : List Bool) : Option BinarySyndromeDecodingInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (checkCount, afterCheckCount) =>
      match (readAtomic afterCheckCount : Option (ℕ × List Bool)) with
      | none => none
      | some (blockLength, afterBlockLength) =>
          match (readAtomic afterBlockLength : Option (ℕ × List Bool)) with
          | none => none
          | some (radius, afterRadius) =>
              match (readFinValues checkCount afterRadius :
                Option ((Fin checkCount → ℤ) × List Bool)) with
              | none => none
              | some (syndrome, afterSyndrome) =>
                  match readMatrixRows checkCount blockLength afterSyndrome with
                  | some (parityCheck, []) =>
                      some {
                        checkCount
                        blockLength
                        parityCheck := fun row column =>
                          (parityCheck row column : ZMod 2)
                        syndrome := fun row => (syndrome row : ZMod 2)
                        radius
                      }
                  | _ => none

@[simp] theorem decodeBinarySyndromeDecodingInstance_encode
    (record : BinarySyndromeDecodingInstance) :
    decodeBinarySyndromeDecodingInstance
      (encodeBinarySyndromeDecodingInstance record) = some record := by
  cases record with
  | mk checkCount blockLength parityCheck syndrome radius =>
      have matrix :
          readMatrixRows checkCount blockLength
              (encodeMatrixRows checkCount blockLength
                (fun row column => ((parityCheck row column).val : ℤ))) =
            some ((fun row column => ((parityCheck row column).val : ℤ)), []) := by
        simpa using
          readMatrixRows_append
            (fun row column => ((parityCheck row column).val : ℤ)) []
      simp only [decodeBinarySyndromeDecodingInstance,
        encodeBinarySyndromeDecodingInstance, List.append_assoc,
        readAtomic_append, readFinValues_append, matrix,
        binaryIntegerRepresentative_cast]

theorem encodeBinarySyndromeDecodingInstance_injective :
    Function.Injective encodeBinarySyndromeDecodingInstance := by
  intro first second same
  simpa using congrArg decodeBinarySyndromeDecodingInstance same

def binaryNearestCodeword
    (record : BinaryNearestCodewordInstance)
    (coefficients : Fin record.generatorRank → ZMod 2) :
    Fin record.blockLength → ZMod 2 :=
  fun index => ∑ column : Fin record.generatorRank,
    record.generator index column * coefficients column

def binaryNearestTarget (record : BinaryNearestCodewordInstance) :
    Fin record.blockLength → ZMod 2 :=
  record.target

def binarySyndromeProduct
    (record : BinarySyndromeDecodingInstance)
    (word : Fin record.blockLength → ZMod 2) :
    Fin record.checkCount → ZMod 2 :=
  fun row => ∑ column : Fin record.blockLength,
    record.parityCheck row column * word column

def binarySyndromeTarget (record : BinarySyndromeDecodingInstance) :
    Fin record.checkCount → ZMod 2 :=
  record.syndrome

noncomputable def binaryCodeGapFactor (blockLength : ℕ) : ℝ :=
  (blockLength : ℝ) ^ ((1 : ℝ) / 200)

-- Definition hole: project body verbatim; body not checked by Comparator.
noncomputable def binaryNearestCodewordPromise : PromiseProblem where
  yes bits :=
    @decide
      (∃ record : BinaryNearestCodewordInstance,
        encodeBinaryNearestCodewordInstance record = bits ∧
        0 < record.blockLength ∧ 0 < record.radius ∧
        ∃ coefficients : Fin record.generatorRank → ZMod 2,
          hammingNorm
            (binaryNearestTarget record -
              binaryNearestCodeword record coefficients) ≤ record.radius)
      (Classical.propDecidable _)
  no bits :=
    @decide
      (∃ record : BinaryNearestCodewordInstance,
        encodeBinaryNearestCodewordInstance record = bits ∧
        0 < record.blockLength ∧ 0 < record.radius ∧
        ∀ coefficients : Fin record.generatorRank → ZMod 2,
          binaryCodeGapFactor record.blockLength *
              (record.radius : ℝ) <
            (hammingNorm
              (binaryNearestTarget record -
                binaryNearestCodeword record coefficients) : ℝ))
      (Classical.propDecidable _)
  disjoint bits positive negative := by
    simp only [decide_eq_true_eq] at positive negative
    obtain ⟨first, hfirst, dimension, _, coefficients, close⟩ := positive
    obtain ⟨second, hsecond, _, _, far⟩ := negative
    have same :=
      encodeBinaryNearestCodewordInstance_injective
        (hfirst.trans hsecond.symm)
    subst second
    have factor : 1 ≤ binaryCodeGapFactor first.blockLength := by
      unfold binaryCodeGapFactor
      apply Real.one_le_rpow
      · exact_mod_cast dimension
      · norm_num
    have radius : (0 : ℝ) ≤ (first.radius : ℝ) := by positivity
    have closeReal :
        (hammingNorm
          (binaryNearestTarget first -
            binaryNearestCodeword first coefficients) : ℝ) ≤
          (first.radius : ℝ) := by
      exact_mod_cast close
    nlinarith [far coefficients]

-- Definition hole: project body verbatim; body not checked by Comparator.
noncomputable def binarySyndromeDecodingPromise : PromiseProblem where
  yes bits :=
    @decide
      (∃ record : BinarySyndromeDecodingInstance,
        encodeBinarySyndromeDecodingInstance record = bits ∧
        0 < record.blockLength ∧ 0 < record.radius ∧
        ∃ word : Fin record.blockLength → ZMod 2,
          binarySyndromeProduct record word = binarySyndromeTarget record ∧
            hammingNorm word ≤ record.radius)
      (Classical.propDecidable _)
  no bits :=
    @decide
      (∃ record : BinarySyndromeDecodingInstance,
        encodeBinarySyndromeDecodingInstance record = bits ∧
        0 < record.blockLength ∧ 0 < record.radius ∧
        (∃ word : Fin record.blockLength → ZMod 2,
          binarySyndromeProduct record word = binarySyndromeTarget record) ∧
        ∀ word : Fin record.blockLength → ZMod 2,
          binarySyndromeProduct record word = binarySyndromeTarget record →
            binaryCodeGapFactor record.blockLength *
                (record.radius : ℝ) < (hammingNorm word : ℝ))
      (Classical.propDecidable _)
  disjoint bits positive negative := by
    simp only [decide_eq_true_eq] at positive negative
    obtain ⟨first, hfirst, dimension, _, word, solution, close⟩ := positive
    obtain ⟨second, hsecond, _, _, _, far⟩ := negative
    have same :=
      encodeBinarySyndromeDecodingInstance_injective
        (hfirst.trans hsecond.symm)
    subst second
    have factor : 1 ≤ binaryCodeGapFactor first.blockLength := by
      unfold binaryCodeGapFactor
      apply Real.one_le_rpow
      · exact_mod_cast dimension
      · norm_num
    have radius : (0 : ℝ) ≤ (first.radius : ℝ) := by positivity
    have closeReal : (hammingNorm word : ℝ) ≤ (first.radius : ℝ) := by
      exact_mod_cast close
    nlinarith [far word solution]

noncomputable def finitePNorm (p : ℚ) {n : ℕ} (vector : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, |vector i| ^ (p : ℝ)) ^ ((p : ℝ)⁻¹)

noncomputable def finitePLatticeDiscrepancy (I : Instance)
    (vector : Fin I.dimension → ℤ) : Fin I.dimension → ℝ := fun i =>
  (I.target i : ℝ) -
    ∑ j : Fin I.dimension, (I.basis i j : ℝ) * (vector j : ℝ)

noncomputable def finitePLatticeDistance (p : ℚ) (I : Instance)
    (vector : Fin I.dimension → ℤ) : ℝ :=
  finitePNorm p (finitePLatticeDiscrepancy I vector)

noncomputable def finitePGapFactor (p : ℚ) (I : Instance) : ℝ :=
  (I.dimension : ℝ) ^ (((200 : ℝ) * (p : ℝ))⁻¹)

-- Definition hole: project body verbatim; body not checked by Comparator.
noncomputable def finitePGapCVPPromise (p : ℚ) (hp : 1 ≤ p) : PromiseProblem where
  yes bits :=
    @decide
      (∃ I : Instance,
        encodeInstance I = bits ∧
          wellFormed I ∧
          ∃ vector : Fin I.dimension → ℤ,
            finitePLatticeDistance p I vector ≤ (I.radius : ℝ))
      (Classical.propDecidable _)
  no bits :=
    @decide
      (∃ I : Instance,
        encodeInstance I = bits ∧
          wellFormed I ∧
          ∀ vector : Fin I.dimension → ℤ,
            finitePGapFactor p I * (I.radius : ℝ) <
              finitePLatticeDistance p I vector)
      (Classical.propDecidable _)
  disjoint bits positive negative := by
    simp only [wellFormed, decide_eq_true_eq] at positive negative
    obtain ⟨first, hfirst, well, vector, close⟩ := positive
    obtain ⟨second, hsecond, _, far⟩ := negative
    have same := encodeInstance_injective (hfirst.trans hsecond.symm)
    subst second
    have exponent : 0 ≤ (((200 : ℝ) * (p : ℝ))⁻¹) := by
      have parameter : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hp)
      positivity
    have factor : 1 ≤ finitePGapFactor p first := by
      unfold finitePGapFactor
      apply Real.one_le_rpow
      · exact_mod_cast well.1
      · exact exponent
    have radius : 0 < (first.radius : ℝ) := by
      exact_mod_cast well.2.2
    nlinarith [far vector]

structure PromiseReduction (language : BitLanguage) (problem : PromiseProblem) where
  map : List Bool → List Bool
  polynomial_time : Nonempty
    (BitTM map)
  completeness : ∀ input, language input → problem.yes (map input)
  soundness : ∀ input, ¬ language input → problem.no (map input)

def IsNPHardPromise (problem : PromiseProblem) : Bool :=
  @decide
    (∀ language : BitLanguage,
      IsNP language → Nonempty (PromiseReduction language problem))
    (Classical.propDecidable _)

theorem gapCVP400IsNPHard : IsNPHardPromise gapCVP400Promise := by
  sorry

theorem binaryNearestCodewordIsNPHard :
    IsNPHardPromise binaryNearestCodewordPromise := by
  sorry

theorem binarySyndromeDecodingIsNPHard :
    IsNPHardPromise binarySyndromeDecodingPromise := by
  sorry

theorem finitePNormGapCVPIsNPHard (p : ℚ) (hp : 1 ≤ p) :
    IsNPHardPromise (finitePGapCVPPromise p hp) := by
  sorry

end Comparator

end

end GapCVP

end

end

#check GapCVP.Comparator.gapCVP400IsNPHard
#check GapCVP.Comparator.binaryNearestCodewordIsNPHard
#check GapCVP.Comparator.binarySyndromeDecodingIsNPHard
#check GapCVP.Comparator.finitePNormGapCVPIsNPHard
#check GapCVP.Comparator.gapCVP400Promise
#check GapCVP.Comparator.binaryNearestCodewordPromise
#check GapCVP.Comparator.binarySyndromeDecodingPromise
#check GapCVP.Comparator.finitePGapCVPPromise
