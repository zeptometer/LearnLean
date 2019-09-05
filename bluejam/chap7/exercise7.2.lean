universe u

namespace hidden

inductive partial_function (α β: Type u)
| mk {} : (α → option β) → partial_function

end hidden
