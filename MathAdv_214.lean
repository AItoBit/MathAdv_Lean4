import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Teorema (Enderton, Herbert, Q24):
    Todo par de órdenes lineales densos numerables sin extremos son isomorfos.
    
    Nota: Se añaden las instancias `[Nonempty α]` y `[Nonempty β]` ya que sin ellas 
    el teorema es lógicamente falso en Lean (por ejemplo, el tipo `Empty` satisface 
    todas las demás propiedades vacuamente, pero no es isomorfo a `ℚ`). -/
theorem Enderton_Herbert_24
    (α β : Type*)
    [LinearOrder α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Countable α]
    [LinearOrder β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Countable β]
    [Nonempty α] [Nonempty β] :
    Nonempty (OrderIso α β) := by
  exact Order.iso_of_countable_dense α β
