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

example : ∀n, even n ↔ even (n * n) := begin
    intro n,
    apply iff.intro,
        intro e_n,
        apply even_times_is_even,
        assumption,
    have n_e_o : even n ∨ odd n := even_or_odd n,
    cases n_e_o,
        intros,
        assumption,
    
end
