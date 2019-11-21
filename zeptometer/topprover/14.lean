-- 14.lean
open nat

def mod2 : ℕ → ℕ
| 0 := 0
| (succ n) := 
    match mod2 n with
    | 0 := 1
    | (succ n) := 0
    end

inductive even : ℕ → Prop
| even_zero : even 0
| even_succ : ∀ n, even n → even (n + 2)

inductive odd : ℕ → Prop
| odd_succ : ∀ n, even n → odd (n + 1)

lemma even_or_odd : ∀n, even n ∨ odd n := begin
    intro n,
    induction n,
        left,
        apply even.even_zero,
    cases n_ih,
        right,
        apply odd.odd_succ,
        assumption,
    left,
    induction n_n,
    cases n_ih,
    apply even.even_succ,
    cases n_ih,
    assumption
end

lemma not_even_and_odd : ∀n, even n → odd n → false := begin
    intros n e_n,
    induction e_n,
        intro o_zero,
        cases o_zero,
    intro o_e_2,
    cases o_e_2,
    cases o_e_2_a,
    simp [nat.add] at *,
    induction o_e_2_a,
    apply e_n_ih,
    apply odd.odd_succ,
    assumption,
    assumption
end

lemma even_plus_even_is_even : ∀n, even n → ∀m, even m → even (n + m) := begin
    intros n e_n,
    induction e_n,
        intros,
        simp,
        assumption,
    intros m em,
    have comm : e_n_n + 2 + m = (e_n_n + m) + 2 := by simp,
    rw comm,
    apply even.even_succ,
    apply e_n_ih,
    assumption
end

lemma even_is_two_times : ∀n, even (2 * n) := begin
    intro n,
    induction n,
        simp,
        apply even.even_zero,
    rw mul_succ,
    have two_is_even : even 2 := even.even_succ 0 even.even_zero,
    apply even_plus_even_is_even;
    assumption
end

lemma even_times_is_even : ∀n, even n → ∀m, even (n * m) := begin
    intros n e_n,
    induction e_n,
        intros,
        simp,
        apply even.even_zero,
    intro m,
    rw right_distrib,
    have e_2_m : even (2 * m) := even_is_two_times m,
    apply even_plus_even_is_even,
    apply e_n_ih,
    assumption
end

lemma even_plus_odd_is_odd(n m : ℕ) : even n → odd m → odd (n + m) := begin
    intro e_n,
    induction e_n,
        intro,
        simp [nat.add],
        assumption,
    intro o_m,
    have comm1 : e_n_n + 2 = 2 + e_n_n := nat.add_comm e_n_n 2,
    have comm : e_n_n + 2 + m = nat.succ(nat.succ(e_n_n + m)) := calc
        e_n_n + 2 + m = 2 + e_n_n + m : by rw comm1
        ...           = 2 + (e_n_n + m) : by rw nat.add_assoc
        ...           = nat.succ (nat.succ (e_n_n + m)) : begin
            rw nat.succ_add,
            congr,
            apply one_add
        end,
    rw comm,
    apply odd.odd_succ,
    induction o_m,
    have comm2 : (e_n_n + (o_m_n + 1)) = succ (e_n_n + o_m_n) := calc
        (e_n_n + (o_m_n + 1)) = e_n_n + (succ o_m_n) : by rw nat.add_succ
        ...                   = succ (e_n_n + o_m_n) : by rw nat.add_succ,
    rw comm2,
    apply even.even_succ,
    apply even_plus_even_is_even,
    assumption,
    assumption
end

lemma odd_times_odd_is_odd (n m : ℕ) : odd(n) → odd(m) → odd(n * m) := begin
    intro n,
    induction n,
    intro o_m,
    rw right_distrib,
    simp,
    rw add_comm,
    apply even_plus_odd_is_odd,
    apply even_times_is_even,
    assumption,
    assumption
end

theorem evenness_is_idempotent : ∀n, even n ↔ even (n * n) := begin
    intro n,
    apply iff.intro,
        intro e_n,
        apply even_times_is_even,
        assumption,
    have n_e_o : even n ∨ odd n := even_or_odd n,
    cases n_e_o,
        intros,
        assumption,
        have n_e_o_sq : odd (n * n) := begin
            apply odd_times_odd_is_odd; assumption
        end,
        intro e_n_sq,
        apply false.elim,
        apply not_even_and_odd,
        assumption,
        assumption
end

lemma even_is_0_in_mod2 (n : ℕ) : even n → mod2 n = 0 := begin
    intro e_n,
    induction e_n,
    simp [mod2],
    rw add_comm,
    simp [mod2],
    rw e_n_ih,
    simp [mod2]
end

lemma odd_is_1_in_mod2 (n : ℕ) : odd n → mod2 n = 1 := begin
    intro o_n,
    induction o_n,
    simp [mod2],
    have p : mod2 o_n_n = 0 := begin
        apply even_is_0_in_mod2,
        assumption
    end,
    rw p,
    simp [mod2]
end

theorem multiplication_in_f2_is_idempotent(n : ℕ) : mod2 n = mod2 (n * n) := begin
    have n_is_even_or_odd : even n ∨ odd n := by apply even_or_odd,
    cases n_is_even_or_odd,
        have e_n_sq : even (n * n) := begin
            apply (iff.elim_left (evenness_is_idempotent n)),
            assumption
        end,
        have mod2_n_0 : mod2 n = 0 := even_is_0_in_mod2 n n_is_even_or_odd,
        have mod2_n_sq_0 : mod2 (n * n) = 0 := even_is_0_in_mod2 (n * n) e_n_sq,
        rw mod2_n_0,
        rw mod2_n_sq_0,
    have o_n_sq : odd(n * n) := odd_times_odd_is_odd n n n_is_even_or_odd n_is_even_or_odd,
    have mod2_n_1 : mod2 n = 1 := odd_is_1_in_mod2 n n_is_even_or_odd,
    have mod2_n_sq_1 : mod2 (n * n) = 1 := odd_is_1_in_mod2 (n * n) o_n_sq,
    rw mod2_n_1,
    rw mod2_n_sq_1
end