From Maniunfold.Has Require Export
  NullaryOperation.

Class HasBot (A : Type) : Type := bot : A.

Typeclasses Transparent HasBot.

Section Context.

Context {A : Type} `{has_bot : HasBot A}.

Global Instance A_has_un : HasNullOp A := bot.

End Context.
