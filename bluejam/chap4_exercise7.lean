#check sub_self

set_option trace.check true

example (x : ℤ) : x * 0 = 0 :=
calc x * 0  = x * (0 - 0)   : by rw sub_self (0:ℤ)
        ... = x * 0 - x * 0 : by rw mul_sub x 0 0
        ... = 0             : by rw sub_self
