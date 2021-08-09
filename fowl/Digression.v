From Coq Require Import
  Lists.List ZArith.ZArith.
From DEZ.Provides Require Export
  LogicalTheorems.

Import ListNotations.

(** Indexed respectful setoid morphism digression... *)

#[global] Instance id_Proper (A : Type) (R : relation A) : Proper (R ==> R) id.
Proof. intuition. Qed.

Equations out (A : Type) (x : A + A) : A :=
  out (inl a) := a;
  out (inr a) := a.

Equations default (A : Type) (a : A) (x : option A) : A :=
  default a (Some b) := b;
  default a None := a.

Equations grespectful_type (A B : Type) (n : nat) : Type :=
  grespectful_type A B O := B;
  grespectful_type A B (S p) := A -> grespectful_type A B p.

(** Uncurried. *)

Equations grespectful1_fix (A B : Type) (P : Prop -> Prop)
  (l : list (relation A)) (R : relation B) :
  relation (grespectful_type A B (length l)) by struct l :=
  grespectful1_fix P [] R :=
    fun f g : grespectful_type A B _ => P 1 -> R f g;
  grespectful1_fix P (R' :: l') R :=
    fun f g : grespectful_type A B _ => forall x y : A,
    grespectful1_fix (fun C : Prop => P (R' x y /\ C)) l' R (f x) (g y).

Equations grespectful1 (A B : Type)
  (l : list (relation A)) (R : relation B) :
  relation (grespectful_type A B (length l)) :=
  grespectful1 l R := grespectful1_fix id l R.

(** Uncurried, more elaborate version that does not produce [_ /\ 1]. *)

Equations grespectful_fix (A B : Type) (P : Prop + Prop -> Prop)
  (l : list (relation A)) (R : relation B) :
  relation (grespectful_type A B (length l)) by struct l :=
  grespectful_fix P [] R :=
    fun f g : grespectful_type A B _ => P (inl (R f g));
  grespectful_fix P (R' :: l') R :=
    fun f g : grespectful_type A B _ => forall x y : A,
    grespectful_fix (fun X : Prop + Prop =>
    match X with
    | inl C => P (inr (R' x y)) -> C
    | inr C => P (inr (R' x y /\ C))
    end) l' R (f x) (g y).

Equations grespectful (A B : Type)
  (l : list (relation A)) (R : relation B) :
  relation (grespectful_type A B (length l)) :=
  grespectful l R := grespectful_fix (fun X : Prop + Prop =>
    match X with
    | inl C => C
    | inr C => C
    end) l R.

(** The elaboration changes nothing. *)

Lemma iff_grespectful1_fix_grespectful_fix (A B : Type)
  (P1 : Prop -> Prop) (P : Prop + Prop -> Prop)
  (IP1 : Proper (_<->_ ==> _<->_) P1)
  (el : forall C : Prop, P (inl C) <-> (P1 1 -> C))
  (er : forall C : Prop, P (inr C) <-> P1 C)
  (l : list (relation A)) (R : relation B)
  (f g : grespectful_type A B (length l)) :
  grespectful1_fix P1 l R f g <-> grespectful_fix P l R f g.
Proof.
  split.
  - revert P1 P IP1 el er R f g;
    induction l as [| R' l' ri];
    intros P1 P IP1 el er R f g r.
    + simp grespectful1_fix grespectful_fix in *.
      apply el. apply r.
    + simp grespectful1_fix grespectful_fix in *.
      intros x y. eapply ri, r.
      * intros C D e. rewrite e. reflexivity.
      * intros C. split.
        -- intros p p1. rewrite and_True_r in p1. apply p. apply er. apply p1.
        -- intros p1 p. apply p1. rewrite and_True_r. apply er. apply p.
      * intros C. split.
        -- intros p. apply er. apply p.
        -- intros p1. apply er. apply p1.
  - revert P1 P IP1 el er R f g;
    induction l as [| R' l' ri];
    intros P1 P IP1 el er R f g r.
    + simp grespectful1_fix grespectful_fix in *.
      apply el. apply r.
    + simp grespectful1_fix grespectful_fix in *.
      intros x y. eapply ri, r.
      * intros C D e. rewrite e. reflexivity.
      * intros C. split.
        -- intros p p1. rewrite and_True_r in p1. apply p. apply er. apply p1.
        -- intros p1 p. apply p1. rewrite and_True_r. apply er. apply p.
      * intros C. split.
        -- intros p. apply er. apply p.
        -- intros p1. apply er. apply p1. Qed.

Lemma iff_grespectful1_grespectful (A B : Type)
  (l : list (relation A)) (R : relation B)
  (f g : grespectful_type A B (length l)) :
  grespectful1 l R f g <-> grespectful l R f g.
Proof.
  unfold grespectful1, grespectful.
  apply iff_grespectful1_fix_grespectful_fix.
  - typeclasses eauto.
  - intros C. unfold "id". intuition.
  - intros C. unfold "id". intuition. Qed.

(** Curried, does not require [grespectful1'_fix]. *)

Equations grespectful'_fix (A B : Type) (P : Prop -> Prop)
  (l : list (relation A)) (R : relation B) :
  relation (grespectful_type A B (length l)) by struct l :=
  grespectful'_fix P [] R :=
    fun f g : grespectful_type A B _ => P (R f g);
  grespectful'_fix P (R' :: l') R :=
    fun f g : grespectful_type A B _ => forall x y : A,
    grespectful'_fix (fun C : Prop => P (R' x y -> C)) l' R (f x) (g y).

Equations grespectful' (A B : Type)
  (l : list (relation A)) (R : relation B) :
  relation (grespectful_type A B (length l)) :=
  grespectful' l R := grespectful'_fix id l R.

(** Currying changes nothing. *)

Lemma iff_grespectful'_fix_grespectful1_fix (A B : Type)
  (P' : Prop -> Prop) (P1 : Prop -> Prop)
  (IP' : Proper (_<->_ ==> _<->_) P')
  (IP1 : Proper (_<->_ ==> _<->_) P1)
  (e1 : forall C : Prop, P' C <-> (P1 1 -> C))
  (e2 : forall C D : Prop, P' (C -> D) <-> (P1 C -> D))
  (l : list (relation A)) (R : relation B)
  (f g : grespectful_type A B (length l)) :
  grespectful'_fix P' l R f g <-> grespectful1_fix P1 l R f g.
Proof.
  split.
  - revert P' P1 IP' IP1 e1 e2 R f g;
    induction l as [| R' l' ri];
    intros P' P1 IP' IP1 e1 e2 R f g r.
    + simp grespectful1_fix grespectful'_fix in *.
      apply e1. apply r.
    + simp grespectful1_fix grespectful'_fix in *.
      intros x y. eapply ri, r.
      * intros C D e. rewrite e. reflexivity.
      * intros C D e. rewrite e. reflexivity.
      * intros C. split.
        -- intros p. rewrite and_True_r. apply e2. apply p.
        -- intros p1. apply e2. rewrite and_True_r in p1. apply p1.
      * intros C D. split.
        -- intros p. rewrite <- impl_and_r in p. apply e2. apply p.
        -- intros p1. apply e2 in p1. rewrite impl_and_r in p1. apply p1.
  - revert P' P1 IP' IP1 e1 e2 R f g;
    induction l as [| R' l' ri];
    intros P' P1 IP' IP1 e1 e2 R f g r.
    + simp grespectful1_fix grespectful'_fix in *.
      apply e1. apply r.
    + simp grespectful1_fix grespectful'_fix in *.
      intros x y. eapply ri, r.
      * intros C D e. rewrite e. reflexivity.
      * intros C D e. rewrite e. reflexivity.
      * intros C. split.
        -- intros p. rewrite and_True_r. apply e2. apply p.
        -- intros p1. apply e2. rewrite and_True_r in p1. apply p1.
      * intros C D. split.
        -- intros p. rewrite <- impl_and_r in p. apply e2. apply p.
        -- intros p1. apply e2 in p1. rewrite impl_and_r in p1. apply p1. Qed.

Lemma iff_grespectful'_grespectful1 (A B : Type)
  (l : list (relation A)) (R : relation B)
  (f g : grespectful_type A B (length l)) :
  grespectful' l R f g <-> grespectful1 l R f g.
Proof.
  unfold grespectful', grespectful1.
  apply iff_grespectful'_fix_grespectful1_fix.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros C. unfold "id". intuition.
  - intros C. unfold "id". intuition. Qed.

(** Now more. *)

Lemma iff_respectful_grespectful'_nil (A B : Type)
  (R : relation B)
  (f g : grespectful_type A B (length [])) :
  R f g <-> grespectful' [] R f g.
Proof.
  unfold "==>", grespectful'. unfold grespectful'_fix. unfold "id".
  intuition. Qed.

(** These lemmas are enough to cover the standard library. *)

#[useless]
Lemma iff_respectful_grespectful'_1 (A B : Type)
  (R0 : relation A) (R : relation B)
  (f g : grespectful_type A B (length [R0])) :
  (R0 ==> R) f g <-> grespectful' [R0] R f g.
Proof.
  unfold "==>", grespectful'. unfold grespectful'_fix. unfold "id".
  intuition. Qed.

#[useless]
Lemma iff_respectful_grespectful'_2 (A B : Type)
  (R0 R1 : relation A) (R : relation B)
  (f g : grespectful_type A B (length [R0; R1])) :
  (R0 ==> R1 ==> R) f g <-> grespectful' [R0; R1] R f g.
Proof.
  unfold "==>", grespectful'. unfold grespectful'_fix. unfold "id".
  intuition. Qed.

#[useless]
Lemma iff_respectful_grespectful'_3 (A B : Type)
  (R0 R1 R2 : relation A) (R : relation B)
  (f g : grespectful_type A B (length [R0; R1; R2])) :
  (R0 ==> grespectful' [R1; R2] R) f g <-> grespectful' [R0; R1; R2] R f g.
Proof.
  unfold "==>", grespectful'. unfold grespectful'_fix. unfold "id".
  intuition. Qed.

Lemma fiber (A : Type) (P Q : A -> Prop)
  (a : forall x : A, P x <-> Q x) :
  (forall x : A, P x) <-> (forall x : A, Q x).
Proof.
  split.
  - intros p x. rewrite <- a. apply p.
  - intros q x. rewrite a. apply q. Qed.

Lemma iff_respectful_grespectful'_fix_cons_what (A B : Type)
  (P : A -> A -> relation A -> Prop -> Prop) (P0 : A -> A -> relation A -> Prop -> Prop)
  (e2 : forall C D : Prop, forall x y : A, forall R : relation A, (C -> P x y R D) <-> P0 x y R (C -> D))
  (R0 : relation A) (l : list (relation A)) (R : relation B)
  (f g : grespectful_type A B (length (R0 :: l))) :
  (forall x y : A, R0 x y -> grespectful'_fix (P x y R0) l R (f x) (g y)) <->
  forall x y : A, grespectful'_fix (fun (C : Prop) => P0 x y R0 (R0 x y -> C)) l R (f x) (g y).
  (* (R0 ==> grespectful'_fix (P x y) l R) f g <-> grespectful'_fix P0 (R0 :: l) R f g. *)
Proof.
  unfold "==>". simp grespectful'_fix. split.
  - revert P P0 e2 R0 R f g;
    induction l as [| R1 l' ri];
    intros P P0 e2 R0 R f g r x y.
    + simp grespectful'_fix in *.
      eapply e2. apply r.
    + simp grespectful'_fix in *.
      revert x y.
      intros x y x0 y0.
      epose proof fun P P0 e2 R f g r => ri P P0 e2 R0 R f g r as ri'.
      revert x y x0 y0.
      epose proof ri' (fun (x y : A) (R : relation A) (C : Prop) => P x y R (R1 x y -> C))
      (fun (x y : A) (R : relation A) (C : Prop) => P0 x y R (R0 x y -> C)) _ as ri'.
      cbn in ri'.
      intros.
      (* This is tricky. *) Admitted.

Lemma iff_respectful_grespectful'_fix_cons (A B : Type)
  (P : Prop -> Prop) (P0 : Prop -> Prop)
  (e2 : forall C D : Prop, (C -> P D) <-> P0 (C -> D))
  (R0 : relation A) (l : list (relation A)) (R : relation B)
  (f g : grespectful_type A B (length (R0 :: l))) :
  (R0 ==> grespectful'_fix P l R) f g <-> grespectful'_fix P0 (R0 :: l) R f g.
Proof.
  unfold "==>". simp grespectful'_fix. split.
  - Admitted.

Lemma iff_respectful_grespectful'_cons (A B : Type)
  (R0 : relation A) (l : list (relation A)) (R : relation B)
  (f g : grespectful_type A B (length (R0 :: l))) :
  (R0 ==> grespectful' l R) f g <-> grespectful' (R0 :: l) R f g.
Proof.
  unfold grespectful', grespectful1. simp grespectful'_fix.
  apply iff_respectful_grespectful'_fix_cons.
  unfold "id".
  intuition. Qed.

(** And now the duals... *)

(** Uncurried. *)

Equations gdisrespectful1_fix (A B : Type) (P : Prop -> Prop)
  (R : relation B) (l : list (relation A)) :
  relation (grespectful_type A B (length l)) by struct l :=
  gdisrespectful1_fix P R [] :=
    fun f g : grespectful_type A B _ => R f g -> P 0;
  gdisrespectful1_fix P R (R' :: l') :=
    fun f g : grespectful_type A B _ => forall x y : A,
    gdisrespectful1_fix (fun C : Prop => P (R' x y \/ C)) R l' (f x) (g y).

Equations gdisrespectful1 (A B : Type)
  (R : relation B) (l : list (relation A)) :
  relation (grespectful_type A B (length l)) :=
  gdisrespectful1 R l := gdisrespectful1_fix id R l.

(** Uncurried, more elaborate version that does not produce [_ \/ 0]. *)

Equations gdisrespectful_fix (A B : Type) (P : Prop + Prop -> Prop)
  (R : relation B) (l : list (relation A)) :
  relation (grespectful_type A B (length l)) by struct l :=
  gdisrespectful_fix P R [] :=
    fun f g : grespectful_type A B _ => P (inl (R f g));
  gdisrespectful_fix P R (R' :: l') :=
    fun f g : grespectful_type A B _ => forall x y : A,
    gdisrespectful_fix (fun X : Prop + Prop =>
    match X with
    | inl C => C -> P (inr (R' x y))
    | inr C => P (inr (R' x y \/ C))
    end) R l' (f x) (g y).

Equations gdisrespectful (A B : Type)
  (R : relation B) (l : list (relation A)) :
  relation (grespectful_type A B (length l)) :=
  gdisrespectful R l := gdisrespectful_fix (fun X : Prop + Prop =>
    match X with
    | inl C => C -> 0
    | inr C => C
    end) R l.

Lemma iff_gdisrespectful1_fix_gdisrespectful_fix (A B : Type)
  (P1 : Prop -> Prop) (P : Prop + Prop -> Prop)
  (IP1 : Proper (_<->_ ==> _<->_) P1)
  (el : forall C : Prop, P (inl C) <-> (C -> P1 0))
  (er : forall C : Prop, P (inr C) <-> P1 C)
  (l : list (relation A)) (R : relation B)
  (f g : grespectful_type A B (length l)) :
  gdisrespectful1_fix P1 R l f g <-> gdisrespectful_fix P R l f g.
Proof.
  split.
  - revert P1 P IP1 el er R f g;
    induction l as [| R' l' ri];
    intros P1 P IP1 el er R f g r.
    + simp gdisrespectful1_fix gdisrespectful_fix in *.
      apply el. apply r.
    + simp gdisrespectful1_fix gdisrespectful_fix in *.
      intros x y. eapply ri, r.
      * intros C D e. rewrite e. reflexivity.
      * intros C. split.
        -- intros p c. rewrite or_False_r. apply er. apply p. apply c.
        -- intros p1 c. rewrite or_False_r in p1. apply er. apply p1. apply c.
      * intros C. split.
        -- intros p. apply er. apply p.
        -- intros p1. apply er. apply p1.
  - revert P1 P IP1 el er R f g;
    induction l as [| R' l' ri];
    intros P1 P IP1 el er R f g r.
    + simp gdisrespectful1_fix gdisrespectful_fix in *.
      apply el. apply r.
    + simp gdisrespectful1_fix gdisrespectful_fix in *.
      intros x y. eapply ri, r.
      * intros C D e. rewrite e. reflexivity.
      * intros C. split.
        -- intros p c. rewrite or_False_r. apply er. apply p. apply c.
        -- intros p1 c. rewrite or_False_r in p1. apply er. apply p1. apply c.
      * intros C. split.
        -- intros p. apply er. apply p.
        -- intros p1. apply er. apply p1. Qed.

Lemma iff_gdisrespectful1_gdisrespectful (A B : Type)
  (R : relation B) (l : list (relation A))
  (f g : grespectful_type A B (length l)) :
  gdisrespectful1 R l f g <-> gdisrespectful R l f g.
Proof.
  unfold gdisrespectful1, gdisrespectful.
  apply iff_gdisrespectful1_fix_gdisrespectful_fix.
  - typeclasses eauto.
  - intros C. unfold "id". intuition.
  - intros C. unfold "id". intuition. Qed.

(** Curried, does not require [grespectful1'_fix]. *)

Equations gdisrespectful'_fix (A B : Type) (P : Prop -> Prop)
  (R : relation B) (l : list (relation A)) :
  relation (grespectful_type A B (length l)) by struct l :=
  gdisrespectful'_fix P R [] :=
    fun f g : grespectful_type A B _ => P (~ R f g);
  gdisrespectful'_fix P R (R' :: l') :=
    fun f g : grespectful_type A B _ => forall x y : A,
    gdisrespectful'_fix (fun C : Prop => P (~ R' x y -> C)) R l' (f x) (g y).

Equations gdisrespectful' (A B : Type)
  (R : relation B) (l : list (relation A)) :
  relation (grespectful_type A B (length l)) :=
  gdisrespectful' R l := gdisrespectful'_fix id R l.

(** Currying changes nothing, but requires decidability. *)

Lemma iff_gdisrespectful'_fix_gdisrespectful1_fix (A B : Type)
  (P' : Prop -> Prop) (P1 : Prop -> Prop)
  (IP' : Proper (_<->_ ==> _<->_) P')
  (IP1 : Proper (_<->_ ==> _<->_) P1)
  (e1 : forall C : Prop, P' (~ C) <-> (C -> P1 0))
  (e2 : forall C D : Prop, Decidable D -> P' (~ D -> ~ C) <-> (C -> P1 D))
  (l : list (relation A)) (R : relation B)
  (Hd' : forall R' : relation A, In R' l -> forall x y : A, Decidable (R' x y))
  (Hd1 : forall x y : B, Decidable (R x y))
  (f g : grespectful_type A B (length l)) :
  gdisrespectful'_fix P' R l f g <-> gdisrespectful1_fix P1 R l f g.
Proof.
  split.
  - revert P' P1 IP' IP1 e1 e2 R Hd' Hd1 f g;
    induction l as [| R' l' ri];
    intros P' P1 IP' IP1 e1 e2 R Hd' Hd1 f g r.
    + simp gdisrespectful1_fix gdisrespectful'_fix in *.
      apply e1. apply r.
    + simp gdisrespectful1_fix gdisrespectful'_fix in *.
      intros x y. assert (Decidable (R' x y)).
      { apply Hd'. left. reflexivity. }
      eapply ri, r.
      * intros C D e. rewrite e. reflexivity.
      * intros C D e. rewrite e. reflexivity.
      * intros C. split.
        -- intros p. rewrite or_False_r. apply e2. typeclasses eauto. apply p.
        -- intros p1. apply e2. typeclasses eauto. rewrite or_False_r in p1. apply p1.
      * intros C D.
          assert (eqr : ~ (R' x y \/ D) <-> ~ R' x y /\ ~ D) by intuition. split.
        -- intros p. rewrite <- impl_and_r in p. apply e2.
          decide (R' x y); decide D.
          exists true. split; auto.
          exists true. split; auto.
          exists true. split; auto.
          exists false. split.
          intros ?; congruence.
          intros [? | ?]; contradiction.
          rewrite eqr. apply p.
        -- intros p1. rewrite <- impl_and_r. rewrite <- eqr. apply e2.
          decide (R' x y); decide D.
          exists true. split; auto.
          exists true. split; auto.
          exists true. split; auto.
          exists false. split.
          intros ?; congruence.
          intros [? | ?]; contradiction.
          apply p1.
      * intros R'' I x' y'. apply Hd'. right. auto.
      * intros x' y'. auto.
  - revert P' P1 IP' IP1 e1 e2 R Hd' Hd1 f g;
    induction l as [| R' l' ri];
    intros P' P1 IP' IP1 e1 e2 R Hd' Hd1 f g r.
    + simp gdisrespectful1_fix gdisrespectful'_fix in *.
      apply e1. apply r.
    + simp gdisrespectful1_fix gdisrespectful'_fix in *.
      intros x y. assert (Decidable (R' x y)).
      { apply Hd'. left. reflexivity. }
      eapply ri, r.
      * intros C D e. rewrite e. reflexivity.
      * intros C D e. rewrite e. reflexivity.
      * intros C. split.
        -- intros p. rewrite or_False_r. apply e2. typeclasses eauto. apply p.
        -- intros p1. apply e2. typeclasses eauto. rewrite or_False_r in p1. apply p1.
      * intros C D.
          assert (eqr : ~ (R' x y \/ D) <-> ~ R' x y /\ ~ D) by intuition. split.
        -- intros p. rewrite <- impl_and_r in p. apply e2.
          decide (R' x y); decide D.
          exists true. split; auto.
          exists true. split; auto.
          exists true. split; auto.
          exists false. split.
          intros ?; congruence.
          intros [? | ?]; contradiction.
          rewrite eqr. apply p.
        -- intros p1. rewrite <- impl_and_r. rewrite <- eqr. apply e2.
          decide (R' x y); decide D.
          exists true. split; auto.
          exists true. split; auto.
          exists true. split; auto.
          exists false. split.
          intros ?; congruence.
          intros [? | ?]; contradiction.
          apply p1.
      * intros R'' I x' y'. apply Hd'. right. auto.
      * intros x' y'. auto. Qed.

Lemma iff_gdisrespectful'_gdisrespectful1 (A B : Type)
  (R : relation B) (l : list (relation A))
  (Hd' : forall R' : relation A, In R' l -> forall x y : A, Decidable (R' x y))
  (Hd : forall x y : B, Decidable (R x y))
  (f g : grespectful_type A B (length l)) :
  gdisrespectful' R l f g <-> gdisrespectful1 R l f g.
Proof.
  unfold gdisrespectful1, gdisrespectful.
  apply iff_gdisrespectful'_fix_gdisrespectful1_fix.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros C. unfold "id". intuition.
  - intros C D ?. unfold "id". decide D; intuition.
  - typeclasses eauto.
  - typeclasses eauto. Qed.

Lemma iff_respectful_gdisrespectful'_nil (A B : Type)
  (R : relation B)
  (f g : grespectful_type A B (length [])) :
  complement R f g <-> gdisrespectful' R [] f g.
Proof.
  unfold "==>", gdisrespectful'. unfold gdisrespectful'_fix. unfold "id".
  intuition. Qed.

#[useless]
Lemma iff_respectful_gdisrespectful_1 (A B : Type)
  (R : relation B) (R0 : relation A)
  (** Do you need both? *)
  (Hd : forall x y : B, Decidable (R x y))
  (Hd0 : forall x y : A, Decidable (R0 x y))
  (f g : grespectful_type A B (length [R0])) :
  (complement R0 ==> complement R) f g <-> gdisrespectful R [R0] f g.
Proof.
  unfold complement, "==>", gdisrespectful.
  unfold gdisrespectful_fix. unfold out.
  split.
  - intros F x y. specialize (F x y).
    decide (R0 x y); intuition.
  - intuition. Qed.

Lemma iff_respectful_gdisrespectful'_cons (A B : Type)
  (R' : relation A) (R : relation B) (l : list (relation A))
  (f g : grespectful_type A B (length (R' :: l))) :
  (complement R' ==> gdisrespectful' R l) f g <-> gdisrespectful' R (R' :: l) f g.
Proof.
  unfold "==>", gdisrespectful'.
  split; intros C.
  - revert R' R f g C. induction l as [| R'' l' Ci]; intros R' R f g C.
    + hnf. intros x y. hnf. unfold "id". specialize (C x y). intuition.
    (** This might go, although it may require decidability. *) Admitted.

Section Suffering.

Import Z. Open Scope Z_scope.

Eval cbv -[le zero opp add const] in grespectful1 [] le one one.
Eval cbv -[le zero opp add const] in grespectful [] le one one.
Eval cbv -[le zero opp add const] in grespectful' [] le one one.
Eval cbv -[le zero opp add const] in le one one.
Eval cbv -[le zero opp add const] in grespectful1 [le] le opp opp.
Eval cbv -[le zero opp add const] in grespectful [le] le opp opp.
Eval cbv -[le zero opp add const] in grespectful' [le] le opp opp.
Eval cbv -[le zero opp add const] in (le ==> le) opp opp.
Eval cbv -[le zero opp add const] in grespectful1 [le; le] le add add.
Eval cbv -[le zero opp add const] in grespectful [le; le] le add add.
Eval cbv -[le zero opp add const] in grespectful' [le; le] le add add.
Eval cbv -[le zero opp add const] in (le ==> le ==> le) add add.

Eval cbv -[le zero opp add const] in gdisrespectful1 le [] one one.
Eval cbv -[le zero opp add const] in gdisrespectful le [] one one.
Eval cbv -[le zero opp add const] in gdisrespectful' le [] one one.
Eval cbv -[le zero opp add const] in complement le one one.
Eval cbv -[le zero opp add const] in gdisrespectful1 le [le] opp opp.
Eval cbv -[le zero opp add const] in gdisrespectful le [le] opp opp.
Eval cbv -[le zero opp add const] in gdisrespectful' le [le] opp opp.
Eval cbv -[le zero opp add const] in (complement le ==> complement le) opp opp.
Eval cbv -[le zero opp add const] in gdisrespectful1 le [le; le] add add.
Eval cbv -[le zero opp add const] in gdisrespectful le [le; le] add add.
Eval cbv -[le zero opp add const] in gdisrespectful' le [le; le] add add.
Eval cbv -[le zero opp add const] in (complement le ==> complement le ==> complement le) add add.

End Suffering.

(** End of digression. *)
