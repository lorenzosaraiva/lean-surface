import Lean
import Mathlib

section

namespace CompactnessConjecture

noncomputable section Foundations

open Filter Finset SimpleGraph

open scoped Topology

structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

noncomputable def familyExtremal (family : Finset FiniteGraph)
    (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (FamilyFree family)).sup
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)

def IsCyclicFamily (family : Finset FiniteGraph) : Prop :=
  ∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic

def IsCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
        C * (familyExtremal family n : ℝ)

def CompactnessConjectureStatement : Prop :=
  ∀ family : Finset FiniteGraph,
    family.Nonempty → IsCyclicFamily family → IsCompactFamily family

end Foundations

noncomputable section Separation

open Filter Finset SimpleGraph

open scoped Topology

def extremalScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((4 : ℝ) / 3)

def UniformMemberLower (family : Finset FiniteGraph) (c : ℝ) : Prop :=
  ∀ forbidden ∈ family,
    ∀ᶠ n : ℕ in atTop,
      c * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ)

end Separation

noncomputable section Counterexample

open SimpleGraph

theorem not_erdos_180 :
    ¬ CompactnessConjectureStatement := by
  sorry

end Counterexample

noncomputable section MainTheorem

open Finset SimpleGraph

open scoped Classical

theorem quantitativeCompactnessCounterexample :
    ∃ (family : Finset FiniteGraph) (c C : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      0 < C ∧
      UniformMemberLower family c ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree family host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal family n : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  sorry

theorem compactnessCounterexample_bigO :
    ∃ (family : Finset FiniteGraph) (c : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      UniformMemberLower family c ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (familyExtremal family n : ℝ))
        (fun n : ℕ =>
          (n : ℝ) ^ ((4 : ℝ) / 3 - (1 : ℝ) / 48)) ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  sorry

end MainTheorem

end CompactnessConjecture

end

#check CompactnessConjecture.quantitativeCompactnessCounterexample
#check CompactnessConjecture.compactnessCounterexample_bigO
#check CompactnessConjecture.not_erdos_180
