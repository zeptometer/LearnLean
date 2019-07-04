def eudclid : ∀ k l m : ℕ, (l ∣ m ∧ l ∣ (m + k)) → l ∣ m ∧ l ∣ k :=
begin
  intros k l m,
  intros h,
  cases h with lm lmk,
  apply and.intro,
  exact lm,
  apply (nat.dvd_add_iff_right lm).mpr,
  exact lmk
end

def factorial_n : ∀ n : ℕ, ∃ m : ℕ, ∀ l : ℕ, l ≤ n → l ∣ m :=
begin
  apply nat.rec,

    apply (exists.intro 0),
    intros l h,
    exact (dvd_zero l),

    intros n h,
    cases h with fact_n h_fact_n,
    apply (exists.intro (fact_n*n.succ)),
    intros l hl,
    cases hl,

      exact (dvd_mul_left n.succ fact_n),

      apply dvd_mul_of_dvd_left,
      exact (h_fact_n l hl_a)
end

def isPrime (n : ℕ) : Prop := n > 1 ∧ ∀ m : ℕ, m < n ∧  m ∣ n → m==1

