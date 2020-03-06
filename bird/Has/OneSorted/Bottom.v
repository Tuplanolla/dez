From Maniunfold.Has Require Export
  Unit.

Class HasBot (A : Type) : Type := bot : A.

Typeclasses Transparent HasBot.

Section Context.

Context {A : Type} `{has_bot : HasBot A}.

Global Instance A_has_un : HasUn A := bot.

End Context.
