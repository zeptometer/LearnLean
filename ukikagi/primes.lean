
definition is_prime (x: ℕ): Prop
:= 1 < x ∧ ∀ y: ℕ, y ∣ x → y = 1 ∨ y = x
 
definition factorial: ℕ → ℕ
| 0 := 1
| (nat.succ n) := nat.succ n * factorial n

lemma pos_factorial (n: ℕ):
  factorial n > 0
:=
begin
  induction n with k ih,
  {
    simp [factorial],
    exact nat.succ_pos 0,
  },
  {
    simp [factorial],
    have hskpos: nat.succ k > 0, from nat.succ_pos k,
    have h: nat.succ k * 0 < nat.succ k * factorial k, from mul_lt_mul_of_pos_left ih hskpos,
    rw (mul_zero (nat.succ k)) at h,
    exact h
  }
end

lemma factorial_division (n: ℕ):
  ∀ m: ℕ, 1 ≤ m → m ≤ n → m ∣ factorial n
:=
begin
  intros m h1 h2,
  induction n with k h3,
    have le10: 1 ≤ 0 := le_trans h1 h2,
    exact absurd le10 (nat.not_succ_le_zero 0),
  simp [factorial],
  cases h2 with _ hlek,
  {
    simp
  },
  {
    apply dvd_mul_of_dvd_right,
    exact h3 hlek
  }
end

lemma construct_prime (n: ℕ) (h: 1 < n):
  ∃ p: ℕ, is_prime p ∧ p ∣ n
:=
begin
  let nontriv_factor := λx, 1 < x ∧ x ∣ n,
  have h: ∃ x: ℕ, nontriv_factor x, by {
    existsi n,
    split,
    exact h,
    simp
  },
  let p := nat.find h,
  let hp := nat.find_spec h,
  have defprev: nat.find h = p, by simp,
  rw [defprev] at hp,
  cases hp with hpos hdvd,
  existsi p,
  split,
  {
    simp [is_prime],
    split,
    {
      exact hpos,
    },
    {
      intros y hyp,
      cases lt_trichotomy 1 y with h1lty hrest,
      {
        right,
        have hpley: p ≤ y, from (nat.find_min' h) (and.intro h1lty (dvd_trans hyp hdvd)),
        have h0ltp: 0 < p, from lt_trans zero_lt_one hpos,
        have hylep: y ≤ p, from (nat.le_of_dvd h0ltp hyp),
        exact le_antisymm hylep hpley
      },
      cases hrest with h1eqy hylt1,
      {
        left,
        exact h1eqy.symm
      },
      {
        exfalso,
        have hyeq0: y = 0, by {
          apply nat.eq_zero_of_le_zero,
          apply nat.le_of_lt_succ,
          exact hylt1
        },
        rw hyeq0 at hyp,
        have hpeq0: p = 0, from eq_zero_of_zero_dvd hyp,
        have h1lt0: 1 < 0, by { rw hpeq0 at hpos, exact hpos },
        exact nat.not_lt_zero 1 h1lt0,
      }
    }
  },
  {
    exact hdvd
  }
end

theorem unbouded_primes:
  ∀ m: ℕ, ∃ p: ℕ, is_prime p ∧ m < p :=
begin
  intro m,
  let a := factorial m + 1,
  have h1lea: 1 < a, by {
    simp [a],
    refine nat.lt_add_of_pos_left _,
    exact pos_factorial m
  },
  have h: ∃ p: ℕ, is_prime p ∧ p ∣ a, from construct_prime a h1lea,
  cases h with p hp,
  cases hp with hprime hpdvda,
  existsi p,
  split,
  {
    exact hprime
  },
  {
    simp [is_prime] at hprime,
    cases lt_or_ge m p with hmltp hmgep,
    {
      exact hmltp,
    }, {
      exfalso,
      have h1ltp: 1 < p, from hprime.left,
      have hdvdfm: p ∣ factorial m, from factorial_division m p (le_of_lt h1ltp) hmgep,
      have hpdvd1: p ∣ 1, by {
        refine (nat.dvd_add_iff_right hdvdfm).mpr hpdvda,
      },
      have hpeq1: p = 1, from nat.eq_one_of_dvd_one hpdvd1,
      rw hpeq1 at h1ltp,
      exact lt_irrefl 1 h1ltp
    }
  }
end
