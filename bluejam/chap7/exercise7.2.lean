universe u

namespace hidden

variables (α β γ : Type u)

example : inhabited bool := inhabited.mk tt
example : inhabited nat := inhabited.mk 0

def partial_composite (f : α → option β) (g : β → option γ) (x : α) : option γ
:= option.rec_on (f x) none (λ x, g x)

end hidden
