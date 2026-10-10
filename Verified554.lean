import Erdos554
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
The definitions below reproduce the transitive definitions used by the Formal Conjectures
statement. The proof specializes the analytic result without importing research placeholders.
-/

namespace SimpleGraph

def TopEdgeLabeling.CliqueFree {V ι : Type*} (C : TopEdgeLabeling V ι) (n : ℕ) : Prop :=
  ∀ i : ι, (C.labelGraph i).CliqueFree n

end SimpleGraph

namespace Erdos183

def ForcesMonochromaticTriangle (n k : ℕ) : Prop :=
  ∀ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), ¬ C.CliqueFree 3

noncomputable def multicolourTriangleRamsey (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesMonochromaticTriangle n k}

end Erdos183

open Filter SimpleGraph
open scoped Topology

namespace Erdos554

def ForcesMonochromaticOddCycle (m k n : ℕ) : Prop :=
  ∀ C : TopEdgeLabeling (Fin m) (Fin k),
    ∃ c : Fin k, cycleGraph (2 * n + 1) ⊑ C.labelGraph c

noncomputable def oddCycleRamsey (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ForcesMonochromaticOddCycle m k n}

/-- The quantitative bounds imply the ratio limit for each fixed n >= 4. -/
theorem ratio_tendsto_zero_of_power_log_bounds (n : ℕ) (hn : 4 ≤ n) (c : ℝ) (hc : 0 < c)
    (h : ∀ᶠ k in atTop,
      (oddCycleRamsey k n : ℝ) ≤ (4 * (n : ℝ)) ^ k * (k : ℝ) ^ ((k : ℝ) / n) ∧
      (c * (k : ℝ) ^ (1 / 3 : ℝ) / Real.log k) ^ k ≤
        (Erdos183.multicolourTriangleRamsey k : ℝ)) :
    Tendsto (fun k : ℕ => (oddCycleRamsey k n : ℝ) /
      (Erdos183.multicolourTriangleRamsey k : ℝ)) atTop (𝓝 0) := by
  apply Bound554.ratio_tendsto_zero_for_n_ge_four
    (fun k => (oddCycleRamsey k n : ℝ))
    (fun k => (Erdos183.multicolourTriangleRamsey k : ℝ)) hn hc
  filter_upwards [h] with k hk
  exact ⟨Nat.cast_nonneg _, hk.1, hk.2⟩

#print axioms ratio_tendsto_zero_of_power_log_bounds

end Erdos554
