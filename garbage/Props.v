Reserved Notation "x 'OP' '[' mo ']' y" (at level 45, no associativity).
Reserved Notation "'ID' '[' mo ']'" (at level 0).
Reserved Notation "'INV' '[' mo ']' x" (at level 35).
Reserved Notation "x 'ADD' '[' mo ']' y" (at level 50, no associativity).
Reserved Notation "'ZERO' '[' mo ']'" (at level 0).
Reserved Notation "'NEG' '[' mo ']' x" (at level 35).
Reserved Notation "x 'MUL' '[' mo ']' y" (at level 40, no associativity).
Reserved Notation "'ONE' '[' mo ']'" (at level 0).
Reserved Notation "'REC' '[' mo ']' x" (at level 35).
Reserved Notation "x 'NPOW' '[' mo ']' n" (at level 30, no associativity).
Reserved Notation "a 'LADD' '[' mo ']' b" (at level 50, no associativity).
Reserved Notation "'LZERO' '[' mo ']'" (at level 0).
Reserved Notation "'LNEG' '[' mo ']' a" (at level 35).
Reserved Notation "a 'LMUL' '[' mo ']' b" (at level 40, no associativity).
Reserved Notation "'LONE' '[' mo ']'" (at level 0).
Reserved Notation "'LREC' '[' mo ']' a" (at level 35).
Reserved Notation "a 'LSMUL' '[' mo ']' x" (at level 45, no associativity).
Reserved Notation "a 'RADD' '[' mo ']' b" (at level 50, no associativity).
Reserved Notation "'RZERO' '[' mo ']'" (at level 0).
Reserved Notation "'RNEG' '[' mo ']' a" (at level 35).
Reserved Notation "a 'RMUL' '[' mo ']' b" (at level 40, no associativity).
Reserved Notation "'RONE' '[' mo ']'" (at level 0).
Reserved Notation "'RREC' '[' mo ']' a" (at level 35).
Reserved Notation "x 'RSMUL' '[' mo ']' a" (at level 45, no associativity).

Reserved Notation "x 'OP' y" (at level 45, no associativity).
Reserved Notation "'ID'" (at level 0).
Reserved Notation "'INV' x" (at level 35).
Reserved Notation "x 'ADD' y" (at level 50, no associativity).
Reserved Notation "'ZERO'" (at level 0).
Reserved Notation "'NEG' x" (at level 35).
Reserved Notation "x 'MUL' y" (at level 40, no associativity).
Reserved Notation "'ONE'" (at level 0).
Reserved Notation "'REC' x" (at level 35).
Reserved Notation "x 'NPOW' n" (at level 30, no associativity).
Reserved Notation "a 'LADD' b" (at level 50, no associativity).
Reserved Notation "'LZERO'" (at level 0).
Reserved Notation "'LNEG' a" (at level 35).
Reserved Notation "a 'LMUL' b" (at level 40, no associativity).
Reserved Notation "'LONE'" (at level 0).
Reserved Notation "'LREC' a" (at level 35).
Reserved Notation "a 'LSMUL' x" (at level 45, no associativity).
Reserved Notation "a 'RADD' b" (at level 50, no associativity).
Reserved Notation "'RZERO'" (at level 0).
Reserved Notation "'RNEG' a" (at level 35).
Reserved Notation "a 'RMUL' b" (at level 40, no associativity).
Reserved Notation "'RONE'" (at level 0).
Reserved Notation "'RREC' a" (at level 35).
Reserved Notation "x 'RSMUL' a" (at level 45, no associativity).

Section Props.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Variables A L R : Type.

Variable op : A -> A -> A.
Notation "x 'OP' y" := (op x y).
Definition assoc : Prop := forall x y z : A,
  (x OP y) OP z = x OP (y OP z).
Definition comm : Prop := forall x y : A,
  y OP x = x OP y.

Variable id : A.
Notation "'ID'" := id.
Definition id_l : Prop := forall x : A,
  ID OP x = x.
Definition id_r : Prop := forall x : A,
  x OP ID = x.

Variable inv : A -> A.
Notation "'INV' x" := (inv x).
Definition inv_l : Prop := forall x : A,
  (INV x) OP x = ID.
Definition inv_r : Prop := forall x : A,
  x OP (INV x) = ID.

Variable add : A -> A -> A.
Variable zero : A.
Variable neg : A -> A.
Variable mul : A -> A -> A.
Variable one : A.
Variable rec : A -> A.
Notation "x 'ADD' y" := (add x y).
Notation "'ZERO'" := zero.
Notation "'NEG' x" := (neg x).
Notation "x 'MUL' y" := (mul x y).
Notation "'ONE'" := one.
Notation "'REC' x" := (rec x).
Definition dist_l : Prop := forall x y z : A,
  x MUL (y ADD z) = (x MUL y) ADD (x MUL z).
Definition dist_r : Prop := forall x y z : A,
  (x ADD y) MUL z = (x MUL z) ADD (y MUL z).

Variable ladd : L -> L -> L.
Variable lzero : L.
Variable lneg : L -> L.
Variable lmul : L -> L -> L.
Variable lone : L.
Variable lrec : L -> L.
Variable lsmul : L -> A -> A.
Notation "a 'LADD' b" := (ladd a b).
Notation "'LZERO'" := lzero.
Notation "'LNEG' a" := (lneg a).
Notation "a 'LMUL' b" := (lmul a b).
Notation "'LONE'" := lone.
Notation "'LREC' a" := (lrec a).
Notation "a 'LSMUL' x" := (lsmul a x).
Definition lsid : Prop := forall x : A,
  LONE LSMUL x = x.
Definition lsassoc : Prop := forall (a b : L) (x : A),
  (a LMUL b) LSMUL x = a LSMUL (b LSMUL x).
Definition lsdist_l : Prop := forall (a : L) (x y : A),
  a LSMUL (x ADD y) = (a LSMUL x) ADD (a LSMUL y).
Definition lsdist_r : Prop := forall (a b : L) (x : A),
  (a LADD b) LSMUL x = (a LSMUL x) ADD (b LSMUL x).

Variable radd : R -> R -> R.
Variable rzero : R.
Variable rneg : R -> R.
Variable rmul : R -> R -> R.
Variable rone : R.
Variable rrec : R -> R.
Variable rsmul : R -> A -> A.
Notation "a 'RADD' b" := (radd a b).
Notation "'RZERO'" := rzero.
Notation "'RNEG' a" := (rneg a).
Notation "a 'RMUL' b" := (rmul a b).
Notation "'RONE'" := rone.
Notation "'RREC' a" := (rrec a).
Notation "x 'RSMUL' a" := (rsmul a x).
Definition rsid : Prop := forall x : A,
  x RSMUL RONE = x.
Definition rsassoc : Prop := forall (a b : R) (x : A),
  x RSMUL (a RMUL b) = (x RSMUL a) RSMUL b.
Definition rsdist_l : Prop := forall (a : R) (x y : A),
  (x ADD y) RSMUL a = (x RSMUL a) ADD (y RSMUL a).
Definition rsdist_r : Prop := forall (a b : R) (x : A),
  x RSMUL (a RADD b) = (x RSMUL a) ADD (x RSMUL b).

Definition sassoc : Prop := forall (a : L) (b : R) (x : A),
  (a LSMUL x) RSMUL b = a LSMUL (x RSMUL b).

End Props.
