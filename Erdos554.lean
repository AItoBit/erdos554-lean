import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

open Filter
open scoped Topology

namespace Bound554

/-- Exponential upper and lower bounds with separated bases force the ratio to zero. -/
theorem ratio_tendsto_zero_of_geometric_bounds
    (f g u v : ℕ → ℝ) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (h : ∀ᶠ k in atTop, 0 ≤ f k ∧ 0 ≤ u k ∧ 0 < v k ∧
      f k ≤ u k ^ k ∧ v k ^ k ≤ g k ∧ u k / v k ≤ q) :
    Tendsto (fun k ↦ f k / g k) atTop (𝓝 0) := by
  have hnonneg : ∀ᶠ k in atTop, 0 ≤ f k / g k := by
    filter_upwards [h] with k hk
    exact div_nonneg hk.1 (le_trans (pow_nonneg hk.2.2.1.le _) hk.2.2.2.2.1)
  apply squeeze_zero' hnonneg _ (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)
  filter_upwards [h] with k hk
  calc
    f k / g k ≤ u k ^ k / v k ^ k :=
      div_le_div₀ (pow_nonneg hk.2.1 _) hk.2.2.2.1
        (pow_pos hk.2.2.1 _) hk.2.2.2.2.1
    _ = (u k / v k) ^ k := (div_pow _ _ _).symm
    _ ≤ q ^ k := pow_le_pow_left₀ (div_nonneg hk.2.1 hk.2.2.1.le) hk.2.2.2.2.2 k

/-- It suffices for the ratio of the bases in exponential bounds to tend to zero. -/
theorem ratio_tendsto_zero_of_base_ratio
    (f g u v : ℕ → ℝ)
    (h : ∀ᶠ k in atTop, 0 ≤ f k ∧ 0 ≤ u k ∧ 0 < v k ∧
      f k ≤ u k ^ k ∧ v k ^ k ≤ g k)
    (huv : Tendsto (fun k ↦ u k / v k) atTop (𝓝 0)) :
    Tendsto (fun k ↦ f k / g k) atTop (𝓝 0) := by
  apply ratio_tendsto_zero_of_geometric_bounds f g u v
    (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ k in atTop, u k / v k < (1 / 2 : ℝ) :=
    huv.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [h, hsmall] with k hk hks
  exact ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2, hks.le⟩

#print axioms ratio_tendsto_zero_of_geometric_bounds
#print axioms ratio_tendsto_zero_of_base_ratio

end Bound554

namespace Bound554

theorem base_ratio_tendsto_zero {a c r s : ℝ} (hc : 0 < c) (hrs : r < s) :
    Tendsto (fun k : ℕ ↦ a * (k : ℝ) ^ r /
      (c * (k : ℝ) ^ s / Real.log k)) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_atTop (sub_pos.mpr hrs)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  have heq : (fun k : ℕ ↦ a * (k : ℝ) ^ r /
      (c * (k : ℝ) ^ s / Real.log k)) =ᶠ[atTop]
      (fun k : ℕ ↦ (a / c) * (Real.log k / (k : ℝ) ^ (s - r))) := by
    filter_upwards [eventually_gt_atTop 1] with k hk
    have hx : 1 < (k : ℝ) := by exact_mod_cast hk
    rw [Real.rpow_sub (lt_trans zero_lt_one hx) s r]
    have hpr := (Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) r).ne'
    have hps := (Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) s).ne'
    have hl := (Real.log_pos hx).ne'
    field_simp [hc.ne', hpr, hps, hl]
  have h' : Tendsto (fun k : ℕ => (a / c) *
      (Real.log k / (k : ℝ) ^ (s - r))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using h.const_mul (a / c)
  exact h'.congr' heq.symm

theorem ratio_tendsto_zero_of_power_log_bounds
    (f g : ℕ → ℝ) {a c r s : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hrs : r < s)
    (h : ∀ᶠ k in atTop, 0 ≤ f k ∧
      f k ≤ a ^ k * (k : ℝ) ^ ((k : ℝ) * r) ∧
      (c * (k : ℝ) ^ s / Real.log k) ^ k ≤ g k) :
    Tendsto (fun k ↦ f k / g k) atTop (𝓝 0) := by
  apply ratio_tendsto_zero_of_base_ratio f g
    (fun k ↦ a * (k : ℝ) ^ r) (fun k ↦ c * (k : ℝ) ^ s / Real.log k)
  · filter_upwards [h, eventually_gt_atTop 1] with k hk hk₁
    have hx : 1 < (k : ℝ) := by exact_mod_cast hk₁
    refine ⟨hk.1, mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      div_pos (mul_pos hc (Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) _))
        (Real.log_pos hx), ?_, hk.2.2⟩
    simpa [mul_pow, mul_comm (k : ℝ) r, Real.rpow_mul_natCast (Nat.cast_nonneg k)]
      using hk.2.1
  · exact base_ratio_tendsto_zero hc hrs

theorem ratio_tendsto_zero_for_n_ge_four
    (f g : ℕ → ℝ) {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ k in atTop, 0 ≤ f k ∧
      f k ≤ (4 * (n : ℝ)) ^ k * (k : ℝ) ^ ((k : ℝ) / n) ∧
      (c * (k : ℝ) ^ (1 / 3 : ℝ) / Real.log k) ^ k ≤ g k) :
    Tendsto (fun k ↦ f k / g k) atTop (𝓝 0) := by
  have hn' : (3 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 3 < 4) hn)
  apply ratio_tendsto_zero_of_power_log_bounds f g
    (a := 4 * (n : ℝ)) (r := 1 / (n : ℝ)) (s := 1 / 3)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hc
    (one_div_lt_one_div_of_lt (by norm_num) hn')
  simpa [div_eq_mul_inv] using h

#print axioms base_ratio_tendsto_zero
#print axioms ratio_tendsto_zero_of_power_log_bounds
#print axioms ratio_tendsto_zero_for_n_ge_four

end Bound554

