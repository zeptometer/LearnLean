namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n


def prime (n : ℕ) : Prop := n > 1 ∧ ¬ ∃ m : ℕ, m ≠ n ∧ m ∣ n

def infinitely_many_primes : Prop := ∀ n : ℕ, ∃ p : ℕ, p > n ∧ prime p

def Fermat_prime (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k + 1 ∧ prime n

def infinitely_many_Fermat_primes : Prop := ∀ n : ℕ, ∃ p : ℕ, p > n ∧ Fermat_prime p

def goldbach_conjecture : Prop
    := ∀ n : ℕ, n > 3 ∧ even n → ∃ p : ℕ, ∃ q : ℕ, prime p ∧ prime q ∧ n = p + q

def Goldbach's_weak_conjecture : Prop
    := ∀ n : ℕ, n > 7 ∧ even n
        → ∃ p : ℕ, ∃ q : ℕ, ∃ r : ℕ, prime p ∧ prime q ∧ prime r ∧ n = p + q + r

def Fermat's_last_theorem : Prop
    := ∀ n : ℕ, n ≥ 3 → ¬ ∃ x : ℕ, ∃ y : ℕ, ∃ z: ℕ, x ^ n + y ^ n = z ^ n

end hidden
