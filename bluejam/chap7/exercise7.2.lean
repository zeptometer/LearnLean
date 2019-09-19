universe u

namespace hidden

variables (α β γ : Type u)

example : inhabited bool := inhabited.mk tt
example : inhabited nat := inhabited.mk 0

def partial_composite : (α → option β) → (β → option γ) → (α → option γ)
:= sorry

end hidden
