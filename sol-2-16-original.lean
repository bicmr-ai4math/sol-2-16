import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.Ring.Defs

theorem a_pow_mn_minus_one{a m d: ℕ}{h₀: 0 < a}: (a ^ m - 1) ∣ (a ^ (m*d) - 1) := by
  induction d with
  | zero =>
  rw[Nat.mul_zero]
  have han: a ^ 0 = 1 := rfl
  have han1: a ^ 0 - 1 = 0 := Nat.sub_eq_of_eq_add han
  exact Iff.mp Nat.modEq_zero_iff_dvd (congrFun (congrArg HMod.hMod han1) (a ^ m - 1))
  | succ d hd =>
  rw[Nat.mul_succ]
  have h₁: a ^ (m * d + m) - 1 = a^m * (a^(m*d)-1)+(a^m-1) := by
    ring_nf
    rw[Nat.sub_one (a ^ (m * d))]
    rw[Nat.mul_pred_right]
    apply Nat.sub_eq_of_eq_add
    rw[add_assoc]
    rw[Nat.sub_add_cancel]
    rw[Nat.sub_add_cancel]
    rw[← Nat.pow_add]
    apply Nat.pow_le_pow_of_le_right h₀
    exact Nat.le_add_right m (m * d)
    exact Nat.one_le_pow m a h₀
  rw[h₁]
  apply Nat.dvd_add
  exact Dvd.dvd.mul_left hd (a ^ m)
  exact Nat.dvd_refl (a ^ m - 1)


lemma upup (d s t: ℕ) (a b : ℤ) (ha: a ≥ 0) (hb: b ≥ 0) (h:   s*a + d = t*b) : ∃ m n : ℕ,   s*m + d=  t*n := by
  use (Int.natAbs a)
  use (Int.natAbs b)
  have haa: Int.natAbs a = a := Int.natAbs_of_nonneg ha
  have hbb: Int.natAbs b = b := Int.natAbs_of_nonneg hb
  rw[← haa, ← hbb] at h
  apply Int.ofNat_inj.1
  apply h


theorem nat_bezout {s t:ℕ }{h₁: 0 < s}{h₂: 0 < t}: ∃ m:ℕ ,∃ n:ℕ , s*m+ s.gcd t=t*n:= by
  let x := Nat.gcdA s t
  let y := Nat.gcdB s t
  have L: ↑ (s.gcd t)=s*x+t*y:= by
    rw[Nat.gcd_eq_gcd_ab]
  have L1 : (↑s) * ((↑t)* (|x|+|y|) - x) + ↑ (s.gcd t) =(↑ t)* ((↑ s) *(|x|+|y|) + y):= by
    rw[L]
    ring
  have L2 : 0 ≤ ((↑t)* (|x|+|y|) - x):= by
    have l2 : x ≤ (↑t)* (|x|+|y|):= by
      calc
      x ≤ |x| := le_abs_self x
      _≤ |x|+|y| := le_add_of_nonneg_right (abs_nonneg y)
      _≤ (↑t)* (|x|+|y|):= by
        have ll2: 1≤ (t:ℤ ):= by
          exact Iff.mp Int.toNat_le h₂
        nth_rw 1 [← one_mul (|x|+|y|)]
        apply mul_le_mul
        exact ll2
        exact Int.le_refl (|x| + |y|)
        apply add_nonneg (abs_nonneg x) (abs_nonneg y)
        exact Int.ofNat_nonneg t
    exact Int.sub_nonneg_of_le l2
  have L3 : 0 ≤ ((↑ s) *(|x|+|y|) + y) := by
    have l3: -y ≤ (↑ s) *(|x|+|y|) := by
      calc
      -y ≤ |y|:= neg_le_abs_self y
      _≤ |x|+|y| := le_add_of_nonneg_left (abs_nonneg x)
      _≤ (↑ s) *(|x|+|y|):= by
        have ll3: 1≤ (s:ℤ ):= by
          exact Iff.mp Int.toNat_le h₁
        nth_rw 1 [← one_mul (|x|+|y|)]
        apply mul_le_mul
        exact ll3
        exact Int.le_refl (|x| + |y|)
        apply add_nonneg (abs_nonneg x) (abs_nonneg y)
        exact Int.ofNat_nonneg s
    exact Iff.mp neg_le_iff_add_nonneg l3
  apply upup (Nat.gcd s t) s t (↑t * (|x| + |y|) - x) (↑s * (|x| + |y|) + y) L2 L3 L1

lemma lemma2161 {a s t m n : ℕ }(h₁ : 0 < a )(h₂ : 0<s)(h₃ : 0 < t)(H: s * m + s.gcd t = t * n)(pp1: (a^s-1).gcd (a^t-1) ∣ (a^(s*m) -1))(pp2: (a^s-1).gcd (a^t-1) ∣ (a^(t*n) -1)): (a^s-1).gcd (a^t-1) ∣  (a^(s.gcd t)-1) := by
  have L1: (a^s-1).gcd (a^t-1) ∣ a^(s.gcd t)* (a^(s*m) -1):= by
    exact Dvd.dvd.mul_left pp1 (a ^ Nat.gcd s t)
  have L2: a^(s.gcd t)* (a^(s*m) -1) ≤ (a^(t*n) -1) := by
    rw[Nat.mul_sub_left_distrib]
    rw[← Nat.pow_add]
    rw[add_comm]
    rw[H]
    rw[mul_one]
    have LL2: 1≤ (a^(s.gcd t)):= by
      exact Nat.one_le_pow (s.gcd t) a h₁
    apply Nat.sub_le_sub_left
    apply LL2
  have L3: (a^(t*n) -1)-a^(s.gcd t)* (a^(s*m) -1)= a^(s.gcd t) -1:= by
    rw[Nat.mul_sub_left_distrib]
    rw[← Nat.pow_add]
    rw[add_comm]
    rw[H]
    rw[mul_one]
    rw[Nat.sub_right_comm]
    rw[Nat.sub_sub_self]
    by_cases p1: a=1
    rw[p1]
    rw[one_pow]
    rw[one_pow]
    have p2: 2 ≤ a:= by
      rw[Nat.two_le_iff]
      constructor
      exact Iff.mp Nat.pos_iff_ne_zero h₁
      apply p1
    rw[Nat.pow_le_iff_le_right]
    by_cases p3: n=0
    exfalso
    rw[p3] at H
    rw[mul_zero] at H
    have H' : 0 < s * m + Nat.gcd s t:= by
      have H1: 0 < s.gcd t:= by
        exact Nat.gcd_pos_of_pos_left t h₂
      have H2: s.gcd t ≤ s * m + s.gcd t:= by
        exact Nat.le_add_left (Nat.gcd s t) (s * m)
      apply lt_of_lt_of_le H1
      apply H2
    have H'': 0 ≠ s * m + Nat.gcd s t:= by
      exact Nat.ne_of_lt H'
    rw[Ne, Not] at H''
    apply H''
    rw[H]
    have h': 1≤ n:= by
      exact Iff.mpr Nat.one_le_iff_ne_zero p3
    have h11: s.gcd t ≤ t:= by
      apply Nat.gcd_le_right
      apply h₃
    have h12: t ≤ t*n:= by
      exact Nat.le_mul_of_pos_right h'
    apply le_trans h11
    apply h12
    apply p2
  rw[← L3]
  apply Nat.dvd_sub
  apply L2
  apply pp2
  apply L1

theorem gcd_sub_one_of_sub_one_gcd (a s t :ℕ )(h₁ : 0 < a )(h₂ : 0<s)(h₃ : 0 < t): a^(s.gcd t)-1 = (a^s-1).gcd (a^t-1):= by
  have i: s.gcd t ∣ s := by
    exact Nat.gcd_dvd_left s t
  rcases i with ⟨ u, nu ⟩
  have j: s.gcd t ∣ t := by
    exact Nat.gcd_dvd_right s t
  rcases j with ⟨ v, nv ⟩
  have H : ∃ m:ℕ ,∃ n:ℕ , s*m+ s.gcd t=t*n := by
    apply nat_bezout
    apply h₂
    apply h₃
  rcases H with ⟨m, H⟩
  rcases H with ⟨n, H⟩
  have l1: a^(s.gcd t)-1 ∣  ((a^s-1).gcd (a^t-1)) := by
    have ll1: a^(s.gcd t)-1 ∣  (a^s-1) := by
      nth_rw 2 [nu]
      apply a_pow_mn_minus_one
      apply h₁
    have ll2: a^(s.gcd t)-1 ∣  (a^t-1) := by
      nth_rw 2 [nv]
      apply a_pow_mn_minus_one
      apply h₁
    exact Nat.dvd_gcd ll1 ll2
  have l2: (a^s-1).gcd (a^t-1) ∣  a^(s.gcd t)-1:= by
    have p1: (a^s -1) ∣ (a^(s*m) -1) := by
      apply a_pow_mn_minus_one
      apply h₁
    have p2: (a^t -1) ∣ (a^(t*n)-1):= by
      apply a_pow_mn_minus_one
      apply h₁
    have pp1: (a^s-1).gcd (a^t-1) ∣ (a^(s*m) -1):= by
      apply dvd_trans (Nat.gcd_dvd_left (a^s-1) (a^t-1))
      apply p1
    have pp2: (a^s-1).gcd (a^t-1) ∣ (a^(t*n) -1):= by
      apply dvd_trans (Nat.gcd_dvd_right (a^s-1) (a^t-1))
      apply p2
    apply lemma2161
    apply h₁
    apply h₂
    apply h₃
    apply H
    apply pp1
    apply pp2
  apply dvd_antisymm
  apply l1
  apply l2
