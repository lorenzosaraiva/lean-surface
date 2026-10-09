import Lean
import Mathlib

namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor
section

namespace MetricCodes

noncomputable section

open scoped BigOperators InnerProductSpace

instance numeralTwoAtLeast : Nat.AtLeastTwo 2 := ⟨by decide⟩

abbrev BinaryWord (n : ℕ) := Fin n → Bool

def hammingDist {n : ℕ} (x y : BinaryWord n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

def IsBinaryCode {n : ℕ} (d : ℕ) (C : Finset (BinaryWord n)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → d ≤ hammingDist x y

def sphericalEntropy (u : ℝ) : ℝ :=
  (1 + u) * Real.logb 2 (1 + u) - u * Real.logb 2 u

def binaryEntropy (u : ℝ) : ℝ :=
  -(u * Real.logb 2 u) -
    (1 - u) * Real.logb 2 (1 - u)

def Gamma (a b : ℝ) : ℝ :=
  ((a - b) * (1 + a + b)) /
    ((1 + 2 * a) * Real.sqrt (a * (1 + a)))

def classicalThreshold (s : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - s ^ 2) - 1) / 2

def hammingGamma (a b : ℝ) : ℝ :=
  (2 * (a - b) * (1 - a - b)) /
    Real.sqrt (a * (1 - a))

end

end MetricCodes

namespace SpherePacking

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory Metric

open scoped ENNReal InnerProductSpace Topology

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

end

end SpherePacking

namespace MetricCodes

noncomputable section

set_option autoImplicit false

open Filter Metric Topology

open scoped BigOperators InnerProductSpace Topology

namespace Hamming

noncomputable def validCodes (n d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact Finset.univ.filter (MetricCodes.IsBinaryCode d)

noncomputable def codeNumber (n d : ℕ) : ℕ :=
  (validCodes n d).sup fun C => C.card

def Feasible (δ a b : ℝ) : Prop :=
  0 ≤ b ∧ b < a ∧ a ≤ (1 : ℝ) / 2 ∧
    1 - 2 * δ < MetricCodes.hammingGamma a b

def rateSet (δ : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible δ a b ∧
    r = MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b}

def variationalRate (δ : ℝ) : ℝ := sInf (rateSet δ)

def binaryRate (δ : ℝ) : ℝ :=
  Filter.limsup
    (fun n : ℕ =>
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ))
    Filter.atTop

end Hamming

end

namespace Johnson

noncomputable section

open scoped BigOperators InnerProductSpace Matrix

def centeredDegree (u : ℝ) : ℝ := 1 - 2 * u

def centeredWeight (α : ℝ) : ℝ := 1 - 2 * α

def centeredSigma (β γ : ℝ) : ℝ := 1 - 2 * β - 2 * γ

def centeredEta (α β γ : ℝ) : ℝ :=
  1 - 2 * α + 2 * β - 2 * γ

def spectralLimit (α β γ u : ℝ) : ℝ :=
  let z := centeredDegree u
  let m := centeredWeight α
  let σ := centeredSigma β γ
  let η := centeredEta α β γ
  (σ * η - m * z ^ 2) ^ 2 /
      (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
    ((z ^ 2 - η ^ 2) * (σ ^ 2 - z ^ 2)) /
      (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2))

def asymptoticThreshold (δ α : ℝ) : ℝ :=
  1 - δ / (2 * α * (1 - α))

def rankPenalty (α β γ : ℝ) : ℝ :=
  α * MetricCodes.binaryEntropy (β / α) +
    (1 - α) * MetricCodes.binaryEntropy (γ / (1 - α))

def shellRate (α β γ u : ℝ) : ℝ :=
  1 - MetricCodes.binaryEntropy α + MetricCodes.binaryEntropy u -
    rankPenalty α β γ

structure AsymptoticParameters (δ α β γ u : ℝ) : Prop where
  distance_pos : 0 < δ
  distance_lt_half : δ < (1 : ℝ) / 2
  weight_gt_distance : δ / 2 < α
  weight_lt_half : α < (1 : ℝ) / 2
  support_nonneg : 0 ≤ β
  support_lt_half : β < α / 2
  complement_nonneg : 0 ≤ γ
  complement_lt_half : γ < (1 - α) / 2
  first_lt_degree : β + γ < u
  degree_lt_weight : u < α
  degree_lt_left : u < α - β + γ
  degree_lt_right : u < 1 - α + β - γ

def IsSpectrallyFeasible (δ α β γ u : ℝ) : Prop :=
  asymptoticThreshold δ α < spectralLimit α β γ u

def Feasible (δ α β γ u : ℝ) : Prop :=
  AsymptoticParameters δ α β γ u ∧
    IsSpectrallyFeasible δ α β γ u

def rateSet (δ : ℝ) : Set ℝ :=
  {r | ∃ α β γ u : ℝ,
    Feasible δ α β γ u ∧ r = shellRate α β γ u}

def variationalRate (δ : ℝ) : ℝ :=
  sInf (rateSet δ)

def mrrwG (v : ℝ) : ℝ :=
  MetricCodes.binaryEntropy ((1 - Real.sqrt (1 - v)) / 2)

def mrrwObjective (δ r : ℝ) : ℝ :=
  1 + mrrwG (r ^ 2) -
    mrrwG (r ^ 2 + 2 * δ * r + 2 * δ)

def mrrwRateSet (δ : ℝ) : Set ℝ :=
  {t | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - 2 * δ ∧
    t = mrrwObjective δ r}

def mrrwRate (δ : ℝ) : ℝ :=
  sInf (mrrwRateSet δ)

def combinedVariationalRate (δ : ℝ) : ℝ :=
  min (MetricCodes.Hamming.variationalRate δ) (variationalRate δ)

end

end Johnson

namespace Spherical

noncomputable section

def Feasible (s a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ s < 2 * MetricCodes.Gamma a b

def rateSet (s : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible s a b ∧
    r = MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b}

def variationalRate (s : ℝ) : ℝ := sInf (rateSet s)

end

end Spherical

end MetricCodes

namespace MetricCodes

namespace Spherical

noncomputable section

open scoped BigOperators

namespace HigherHierarchy

def quadraticCoordinate (u : ℝ) : ℝ := u * (1 + u)

def spectralAtom (u : ℝ) : ℝ :=
  Real.sqrt (quadraticCoordinate u) / (1 + 2 * u)

def Interlacing {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : Prop :=
  0 ≤ a (Fin.last r) ∧
    ∀ i : Fin r, a i.castSucc > b i ∧ b i > a i.succ

def lagrangeNumerator {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  ∏ m : Fin r, (quadraticCoordinate (a ℓ) - quadraticCoordinate (b m))

def lagrangeDenominator {r : ℕ}
    (a : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) : ℝ :=
  ∏ m : Fin r,
    (quadraticCoordinate (a ℓ) - quadraticCoordinate (a (ℓ.succAbove m)))

def lagrangeWeight {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  lagrangeNumerator a b ℓ / lagrangeDenominator a ℓ

def Gamma {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ * spectralAtom (a ℓ)

def Phi {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  (∑ ℓ : Fin (r + 1), MetricCodes.sphericalEntropy (a ℓ)) -
    ∑ m : Fin r, MetricCodes.sphericalEntropy (b m)

end HigherHierarchy

end

end Spherical

end MetricCodes

set_option autoImplicit false

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option linter.unusedTactic false

set_option linter.unreachableTactic false

set_option linter.unnecessarySeqFocus false

set_option linter.unnecessarySimpa false

namespace SpherePacking

noncomputable section

set_option autoImplicit false

open scoped BigOperators InnerProductSpace

structure SphericalCode (n : ℕ) (s : ℝ) where
  points : Finset (Euclidean n)
  unit_norm : ∀ x ∈ points, ‖x‖ = 1
  inner_le : ∀ x ∈ points, ∀ y ∈ points, x ≠ y →
    ⟪x, y⟫_ℝ ≤ s

end

end SpherePacking

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace

namespace SpherePacking

def sphericalCodeNumber (n : ℕ) (s : ℝ) : ℕ∞ :=
  ⨆ C : SphericalCode n s, (C.points.card : ℕ∞)

end SpherePacking

end

namespace MetricCodes

namespace Spherical

noncomputable section

open scoped InnerProductSpace Topology

namespace SidelnikovLocalization

def sliceCost (s t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 ((1 - t) / (1 - s))

def localizedEnvelope (κ : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf ((fun t => κ t + sliceCost s t) '' Set.Icc 0 s)

end SidelnikovLocalization

end

namespace HigherHierarchy

noncomputable section

open Filter Topology

open scoped BigOperators Topology

def levelRateSet (r : ℕ) (s : ℝ) : Set ℝ :=
  {R | ∃ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s < 2 * Gamma a b ∧ R = Phi a b}

def levelRate (r : ℕ) (s : ℝ) : ℝ := sInf (levelRateSet r s)

end

noncomputable section

open Filter Topology

open scoped BigOperators Topology

def closedHierarchyRateSet (s : ℝ) : Set ℝ :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s ≤ 2 * Gamma a b ∧ z = Phi a b}

def closedHierarchyVariationalRate (s : ℝ) : ℝ :=
  sInf (closedHierarchyRateSet s)

def sphericalCodeRate (s : ℝ) : ℝ :=
  Filter.limsup
    (fun n : ℕ =>
      Real.logb 2
        ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) / (n : ℝ))
    Filter.atTop

end

noncomputable section

def localizedLevelRate (r : ℕ) (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    (levelRate r) s

def localizedHierarchyRate (s : ℝ) : ℝ :=
  sInf (Set.range fun r : ℕ => localizedLevelRate r s)

def localizedRowRate (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    MetricCodes.Spherical.variationalRate s

def classicalLocalizedRate (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    (fun t => MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold t)) s

end

end HigherHierarchy

end Spherical

end MetricCodes

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option autoImplicit false

set_option maxHeartbeats 1800000

set_option autoImplicit false

set_option maxHeartbeats 1800000

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option autoImplicit false

set_option maxHeartbeats 1800000

set_option autoImplicit false

set_option maxHeartbeats 8000000

namespace MetricCodes

namespace Spherical

noncomputable section

open Filter Topology

open scoped Topology

namespace HigherHierarchy

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor

theorem main_general {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ {r : ℕ} {R : ℝ}
      (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → s < 2 * Gamma a b → Phi a b < R →
        ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
          (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))) ∧
      sphericalCodeRate s ≤ closedHierarchyVariationalRate s := by
  sorry

theorem strict_hierarchy {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  sorry

end HigherHierarchy

end

end Spherical

end MetricCodes

noncomputable section

open Filter Topology

open scoped Topology

namespace SpherePacking

def kissingNumber (n : ℕ) : ℕ∞ :=
  sphericalCodeNumber n ((1 : ℝ) / 2)

end SpherePacking

namespace MetricCodes.Johnson

theorem main_binary_theorem {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    MetricCodes.Hamming.binaryRate δ ≤ combinedVariationalRate δ ∧
      combinedVariationalRate δ < mrrwRate δ := by
  sorry

end MetricCodes.Johnson

namespace MetricCodes.Spherical.HigherHierarchy.NumericalMaximum

theorem eventually_kissingNumber_lt_published :
    ∀ᶠ n : ℕ in atTop,
      ((SpherePacking.kissingNumber n).toNat : ℝ) ≤
        (2 : ℝ) ^ ((0.39661 : ℝ) * (n : ℝ)) := by
  sorry

end MetricCodes.Spherical.HigherHierarchy.NumericalMaximum

end

end

#check MetricCodes.Johnson.main_binary_theorem
#check MetricCodes.Spherical.HigherHierarchy.main_general
#check MetricCodes.Spherical.HigherHierarchy.strict_hierarchy
#check MetricCodes.Spherical.HigherHierarchy.NumericalMaximum.eventually_kissingNumber_lt_published
