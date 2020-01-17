From Maniunfold.Has Require Export
  Function.

Class HasProp (A : Type) : Type := prop : A -> Prop.

Typeclasses Transparent HasProp.

Section Context.

Context {A : Type} `{has_prop : HasProp A}.

Global Instance prop_has_fn : HasFn A Prop := prop.

End Context.
