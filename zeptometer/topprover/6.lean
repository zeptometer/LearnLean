lemma no_space_in_one : ∀ n m : ℕ , ¬ (n < m ∧ nat.succ n > m) := begin
    intros n,
    induction n, {
        intros m,
        intro h,
        cases m,
        cases h.left,
        cases h.right,
        cases a
    }, {
        intros m,
        intro h,
        induction m,
        cases h.left,
        have pl : n_n < m_n := begin
            apply nat.lt_of_succ_lt_succ,
            exact h.left,
        end,
        have pr : nat.succ n_n > m_n := begin
            apply nat.lt_of_succ_lt_succ,
            exact h.right
        end,
        apply n_ih m_n,
        constructor;
        assumption
    }
end

example : ∀ n m : ℕ , n < m ∨ n = m ∨ n > m := begin
    intros n,
    induction n, {
        intros m,
        induction m,
        {simp},
        cases m_ih, {
            left,
            apply nat.lt.step,
            assumption
        }, {
            cases m_ih, {
                left,
                rw ←m_ih,
                apply nat.lt.base
            }, {
                cases m_ih
            }
        }
    }, {
        intros m,
        induction m,
        right, right,
        apply nat.zero_lt_succ,
        cases m_ih, {
            left,
            apply nat.lt.step,
            assumption
        }, {
            cases m_ih, {
                left,
                rw m_ih,
                apply nat.lt.base
            }, {
                have n_ih2 := n_ih m_n,
                cases n_ih2, {
                    have f : false := begin
                        apply no_space_in_one,
                        constructor,
                        assumption,
                        apply nat.succ_lt_succ,
                        assumption
                    end,
                    trivial
                }, {
                    cases n_ih2, {
                        right, left,
                        rw n_ih2
                    }, {
                        right, right,
                        apply nat.succ_lt_succ,
                        assumption
                    }
                }
            }
        }
    }
end
