open bool
constant true_is_false : tt = ff 

example : false := begin
    have n: tt = ff, from true_is_false,
    have m: tt ≠ ff, begin 
        cases n
    end,
    contradiction
end

#print axioms