-- 14.lean
open nat

def mod2 : ℕ → ℕ
| 0 := 0
| (succ n) := 
    match mod2 n with
    | 0 := 1
    | (succ n) := 0
    end

mutual inductive even, odd
with even : ℕ → Prop
| even_zero : even 0
| even_succ : ∀ n, odd n → even (n + 1)
with odd : ℕ → Prop
| odd_succ : ∀ n, even n → odd (n + 1)

mutual lemma succ_even_odd, succ_odd_even
with succ_even_odd : ∀n, even (n + 1) → odd n
| n := begin
    intro n_succ_even,
    cases n_succ_even,
    assumption
end
with succ_odd_even : ∀n, odd (n + 1) → even n
| n := begin
    intro n_succ_odd,
    cases n_succ_odd,
    assumption
end

mutual lemma even_add_preserves_evenness, odd_add_switches_evenness
with even_add_preserves_evenness
    : ∀n, even n → ∀m, even m ↔ even (n + m)
| n := begin
    induction n,
        intro,
        simp,
    intro n_n_succ_is_even,
    simp [add_succ],
    
end
with odd_add_switches_evenness
    : ∀n, odd n = tt → ∀m, even m ↔ odd (n + m)
| _ := begin
    sorry
end

lemma even_addition_preserves_evenness :
    ∀n, even n = tt → ∀m, even m = even (n + m) := begin
        intro n,
        induction n,
        intro,
        intro m,
        simp,
        simp [even, add_succ],   
        intro n_is_odd,
        induction n_n,
        simp [even, odd] at n_is_odd,
        cases n_is_odd,
        simp [odd, add_succ],
        simp [odd] at n_is_odd,
        revert n_is_odd,
        simp [even, add_succ] at n_ih,
        
    end

lemma pohe : ∀n m, even n = even m → ∀l, even l = even (n + m + l) := begin
    intros n m,
    induction n,
    induction m,
        intros,
        simp,
    intro h,

end

example : ∀n, even n = even (n * n) := begin
    intro n,
    induction n,
        simp,
        rw succ_mul,
        rw mul_succ,

end
