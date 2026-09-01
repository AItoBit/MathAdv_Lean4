import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema de Cantor (Método de Back-and-Forth):
    Cualesquiera dos órdenes lineales densos numerables sin extremos
    (mínimo ni máximo) son estrictamente orden-isomorfos. -/
axiom cantor_back_and_forth_isomorphism
    (α β : Type*)
    [LinearOrder α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Countable α]
    [LinearOrder β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Countable β] :
    Nonempty (OrderIso α β)

/-- Teorema (Enderton, Herbert, Q24):
    Todo par de órdenes lineales densos numerables sin extremos son isomorfos. -/
theorem Enderton_Herbert_24
    (α β : Type*)
    [LinearOrder α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Countable α]
    [LinearOrder β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Countable β] :
    Nonempty (OrderIso α β) := by
  exact cantor_back_and_forth_isomorphism α β
