import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Lattice

theorem a_pow_mn_minus_one {m n : ℕ} {a : ℤ} (h : m ∣ n) : (a ^ m - 1) ∣ (a ^ n - 1) := by
  have hmd {d : ℕ}: a ^ m - 1 ∣ a ^ (m * d) - 1 := by
    induction' d with d hd
    have hm0: m * Nat.zero = 0 := by apply Nat.mul_zero
    rw[hm0]
    exact Int.ModEq.dvd rfl
    rcases hd with ⟨l,hl⟩
    have hl: a ^ (m * d) = (a ^ m - 1) * l + 1 := Iff.mp sub_eq_iff_eq_add hl
    use l * a ^ m + 1
    calc
      _ = a ^ (m * d + m) - 1 := rfl
      _ = a ^ (m * d) * (a ^ m) - 1 := by rw[pow_add a (m * d) m]
      _ = ((a ^ m - 1) * l + 1) * (a ^ m) - 1 := by rw[hl]
      _ = (a ^ m - 1) * (l * a ^ m + 1) := by ring
  rcases h with ⟨d,hd⟩
  rw[hd]
  apply hmd

lemma upup (d s t: ℕ) (a b : ℤ) (ha: a ≥ 0) (hb: b ≥ 0) (h: s * a + d = t * b) :
      ∃ m n : ℕ, s * m + d =  t * n := by
  use (Int.natAbs a); use (Int.natAbs b)
  rw[← (Int.natAbs_of_nonneg ha), ← (Int.natAbs_of_nonneg hb)] at h
  apply Int.ofNat_inj.1
  apply h

theorem Nat.bezout {s t : ℕ } (h₂: 0 < t): ∃ m : ℕ ,∃ n : ℕ , s * m + Nat.gcd s t = t * n:= by
  by_cases h₁: s ≤ 0
  have h₁: s = 0 := Iff.mp Nat.le_zero h₁
  rw[h₁]
  use 0; use 1; rfl
  push_neg at h₁
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

theorem gcd_sub_one_of_sub_one_gcd (a : ℤ) (s t : ℕ ) :
      Int.natAbs (a ^ (s.gcd t) - 1) = Int.gcd (a ^ s - 1) (a ^ t - 1):= by
  by_cases ht: t ≤ 0
  have ht: t = 0 := Iff.mp Nat.le_zero ht
  simp[ht, Nat.gcd_zero_right s]
  push_neg at ht
  have hsd: a ^ Nat.gcd s t - 1 ∣ a ^ s - 1 := by apply a_pow_mn_minus_one (Nat.gcd_dvd_left s t)
  have htd: a ^ Nat.gcd s t - 1 ∣ a ^ t - 1 := by apply a_pow_mn_minus_one (Nat.gcd_dvd_right s t)
  have hmn: ∃ m n : ℕ , s * m + Nat.gcd s t = t * n := by apply Nat.bezout ht
  rcases hmn with ⟨m, hmn⟩; rcases hmn with ⟨n, hmn⟩
  have hast: a ^ (s * m) * (a ^ Nat.gcd s t - 1) = a ^ (t * n) - 1 - (a ^ (s * m) - 1) := by calc
    _ = a ^ (s * m + Nat.gcd s t) - 1 - (a ^ (s * m) - 1):= by ring
    _ = a ^ (t * n) - 1 - (a ^ (s * m) - 1) := by rw[hmn]
  have h: a ^ s - 1 ∣ a ^ (s * m) - 1 := by apply a_pow_mn_minus_one (Nat.dvd_mul_right s m)
  have hsm : ↑(Int.gcd (a ^ s - 1) (a ^ t - 1)) ∣ a ^ (s * m) - 1 := by
    exact Int.dvd_trans (Int.gcd_dvd_left (a ^ s - 1) (a ^ t - 1)) h
  have h: a ^ t - 1 ∣ a ^ (t * n) - 1 := by apply a_pow_mn_minus_one (Nat.dvd_mul_right t n)
  have htn: ↑(Int.gcd (a ^ s - 1) (a ^ t - 1)) ∣ a ^ (t * n) - 1 := by
    exact Int.dvd_trans (Int.gcd_dvd_right (a ^ s - 1) (a ^ t - 1)) h
  have h0: ↑(Int.gcd (a ^ s - 1) (a ^ t - 1)) ∣ a ^ (s * m) * (a ^ Nat.gcd s t - 1) := by
    rw[hast]; exact Int.dvd_sub htn hsm
  have h1: ↑(Int.gcd (a ^ s - 1) (a ^ t - 1)) ∣ (a ^ Nat.gcd s t - 1) * ( a ^ (s * m) - 1) := by
    exact Dvd.dvd.mul_left hsm (a ^ Nat.gcd s t - 1)
  have h2 := Int.dvd_sub h0 h1
  ring_nf at h2
  rw[neg_add_eq_sub 1 (a ^ s), neg_add_eq_sub 1 (a ^ t), neg_add_eq_sub 1 (a ^ Nat.gcd s t)] at h2
  exact Nat.dvd_antisymm (Iff.mp Int.ofNat_dvd_right (Int.dvd_gcd hsd htd)) (Iff.mp Int.ofNat_dvd_left h2)

theorem two_pow_n_mius_one {n : ℕ} (hn : n > 1): ¬ ↑n ∣ (2 : ℤ) ^ n - 1 := by
  intro h
  by_cases h2 : (2 : ℤ) ∣ n
  have h1: n - 1 + 1 = n := tsub_add_cancel_of_le (Nat.one_le_of_lt hn)
  · rcases (dvd_trans h2 h) with ⟨d, hd⟩
    have hnd: 2 * (2 ^ (n - 1) - d) = 1 := by
      calc
        _ = 2 * 2 ^ (n - 1) - 2 * d := by ring
        _ = 2 ^ (n - 1 + 1) - 2 * d := by rw[Eq.symm (pow_succ 2 (n - 1))]
        _ = 2 ^ n - (2 ^ n - 1) := by rw[h1, hd]
        _ = 1 := by ring
    have h21: (2 : ℤ) ∣ 1 := by use 2 ^ (n - 1) - d; apply id (Eq.symm hnd)
    apply Prime.not_dvd_one Int.prime_two h21
  · let p := Nat.minFac n
    have hp: Nat.Prime p := Nat.minFac_prime (ne_of_gt hn)
    have hpn: p ∣ n := Nat.minFac_dvd n
    have podd: Nat.coprime p 2 ∨ p ∣ 2 := by apply Nat.coprime_or_dvd_of_prime hp 2
    rcases podd with podd|podd
    · have podd: Nat.coprime 2 p := Iff.mpr Nat.coprime_comm podd
      have podd: IsCoprime (2 : ℤ) p := by
        apply Int.coprime_iff_nat_coprime.2
        apply podd
      have hfl: 2 ^ (p - 1) ≡ 1 [ZMOD p] := by apply Int.ModEq.pow_card_sub_one_eq_one hp podd
      have hfl: ↑p ∣ (2 : ℤ) ^ (p - 1) - 1 := Int.ModEq.dvd (id (Int.ModEq.symm hfl))
      have hp2n1: ↑p ∣ (2 : ℤ) ^ n - 1 := by apply dvd_trans (Iff.mpr Int.ofNat_dvd hpn) h
      have pgcd: (p : ℤ) ∣ ((2 : ℤ) ^ (p - 1) - 1).gcd (2 ^ n - 1) := Int.dvd_gcd hfl hp2n1
      have heq: Int.natAbs ((2 : ℤ) ^ ((p - 1).gcd n) - 1) = Int.gcd ((2 : ℤ) ^ (p - 1) - 1) (2 ^ n - 1)
        := by apply gcd_sub_one_of_sub_one_gcd 2 (p - 1) n
      have hpmn: (p - 1).gcd n = 1 := by
        let d := (p - 1).gcd n
        have hp1: p - 1 > 0 := Nat.sub_pos_of_lt (Nat.Prime.one_lt hp)
        have : p > 0 := Nat.minFac_pos n
        have hdp: d ≤ p - 1 := Nat.le_of_dvd hp1 (Nat.gcd_dvd_left (p - 1) n)
        have hdp: d < p := Iff.mpr (Nat.lt_iff_le_pred (Nat.minFac_pos n)) hdp
        by_cases hd : d ≥ 2
        exfalso
        have hdpc: d ≥ p := by apply Nat.minFac_le_of_dvd hd (Nat.gcd_dvd_right (p - 1) n)
        linarith
        have hd: d ≤ 1 := Iff.mp Nat.not_lt hd
        by_cases hd0 : d = 0
        exfalso
        rw[(Iff.mp Nat.gcd_eq_zero_iff hd0).2] at hn
        linarith
        apply Nat.le_antisymm hd (Iff.mpr Nat.one_le_iff_ne_zero hd0)
      have h211: (2 : ℤ) ^ (Nat.gcd (p - 1) n) - 1 = 1 := by rw[hpmn]; ring
      rw[h211] at heq
      rw[← heq] at pgcd
      have : Prime (p : ℤ) := Iff.mp Nat.prime_iff_prime_int hp
      apply Prime.not_dvd_one (Iff.mp Nat.prime_iff_prime_int hp) pgcd
    · have pe2: p = 2 := Iff.mp (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two) podd
      exact h2 (Iff.mpr Int.ofNat_dvd_right (Iff.mp (Nat.minFac_eq_two_iff n) pe2))