universe u

namespace hidden

variables {α β γ : Type u}

example : inhabited bool := inhabited.mk tt
example : inhabited nat := inhabited.mk 0

def partial_composite (f : α → option β) (g : β → option γ) (x : α) : option γ
:= option.rec_on (f x) none (λ x, g x)

def func1 (n : nat) : option nat := cond (2 ∣ n) (some n) none
def func2 (n : nat) : option nat := cond (4 ∣ n) (some n) none

def f12 : nat → option nat := partial_composite func1 func2

#eval f12 2
#eval f12 3
#eval f12 4
#eval f12 8
#eval f12 9

end hidden
