(** * Extensionality and Univalence *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.ProofIrrelevance
  Logic.PropExtensionality Logic.PropExtensionalityFacts.
From DEZ.Is Require Export
  Irrelevant Isomorphic.

(** TODO Clean up this mess. *)

(** We declare various axiom schemes as classes
    in hopes of one day turning them into theorems. *)

Definition transport (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) (a : P x) : P y.
Proof. induction e. apply a. Defined.

Reserved Notation "x '_*'" (left associativity, at level 20).
Reserved Notation "x '~=' y" (no associativity, at level 70).

#[local] Notation "'_*_'" := (transport _) (only parsing).
#[local] Notation "e '_*'" := (transport _ e) (only parsing).

Module End.

#[local] Notation "'_~=_'" := (fun A B : Type => IsEquivTypes A B _=_ _=_).
#[local] Notation "A '~=' B" := (IsEquivTypes A B _=_ _=_).

Definition applicate (A B : Type) `{!A ~= B} (x : A) : inhabited B.
Proof.
  pose proof equiv_types_bi_inv A B _=_ _=_ as a.
  destruct a as [f IBI]. apply inhabits. apply f. apply x. Defined.

Arguments applicate {_ _} _ _.

(** We define these instances as explicitly as possible,
    because they are used in the univalence axiom. *)

Section Context.

Context (A : Type).

#[export] Instance is_proper_eq_id :
  IsProper (A := A -> A) (_=_ ==> _=_) id.
Proof. intros x y a. apply a. Defined.

Arguments is_proper_eq_id [_ _] _.

#[export] Instance is_retr_eq_id :
  IsRetr (A := A) _=_ id id.
Proof. intros x. apply id%type. Defined.

#[export] Instance is_sect_eq_id :
  IsSect (A := A) _=_ id id.
Proof. intros x. apply id%type. Defined.

#[export] Instance is_iso_l_eq_id :
  IsIsoL (A := A) (B := A) _=_ _=_ id id.
Proof.
  split.
  - apply is_proper_eq_id.
  - apply is_retr_eq_id. Defined.

#[export] Instance is_iso_r_eq_id :
  IsIsoR (A := A) (B := A) _=_ _=_ id id.
Proof.
  split.
  - apply is_proper_eq_id.
  - apply is_sect_eq_id. Defined.

#[export] Instance is_bi_inv_eq_id :
  IsBiInv (A := A) (B := A) _=_ _=_ id.
Proof.
  split.
  - exists id. apply is_iso_l_eq_id.
  - exists id. apply is_iso_r_eq_id. Defined.

End Context.

Section Context.

Context (A B : Type) (e : A = B).

#[export] Instance is_proper_eq_transport_id :
  IsProper (A := A -> B) (_=_ ==> _=_) (transport id e).
Proof. intros x y a. induction a. apply id%type. Defined.

Arguments is_proper_eq_transport_id [_ _] _.

#[export] Instance is_proper_eq_transport_id_sym :
  IsProper (A := B -> A) (_=_ ==> _=_) (transport id (e ^-1)).
Proof. intros x y a. induction a. apply id%type. Defined.

Arguments is_proper_eq_transport_id_sym [_ _] _.

#[export] Instance is_retr_eq_transport_id :
  IsRetr _=_ (transport id e) (transport id (e ^-1)).
Proof. intros x. destruct e. apply id%type. Defined.

#[export] Instance is_sect_eq_transport_id :
  IsSect _=_ (transport id e) (transport id (e ^-1)).
Proof. intros x. destruct e. apply id%type. Defined.

#[export] Instance is_iso_l_eq_transport_id :
  IsIsoL _=_ _=_ (transport id e) (transport id (e ^-1)).
Proof.
  split.
  - apply is_proper_eq_transport_id.
  - apply is_retr_eq_transport_id. Defined.

#[export] Instance is_iso_r_eq_transport_id :
  IsIsoR _=_ _=_ (transport id e) (transport id (e ^-1)).
Proof.
  split.
  - apply is_proper_eq_transport_id_sym.
  - apply is_sect_eq_transport_id. Defined.

#[export] Instance is_bi_inv_eq_transport_id :
  IsBiInv _=_ _=_ (transport id e).
Proof.
  split.
  - exists (transport id (e ^-1)). apply is_iso_l_eq_transport_id.
  - exists (transport id (e ^-1)). apply is_iso_r_eq_transport_id. Defined.

#[export] Instance idtoeqv : A ~= B.
Proof. exists (transport id e). apply is_bi_inv_eq_transport_id. Defined.

End Context.

#[export] Instance is_refl_equiv_types_eq : IsRefl _~=_.
Proof. intros A. exists id. apply is_bi_inv_eq_id. Defined.

#[export] Instance is_sym_equiv_types_eq : IsSym _~=_.
Proof.
  intros A B [f [[g IR] [h IS]]]. exists (g o f o h). split.
  - exists f. split.
    + typeclasses eauto.
    + intros y. unfold compose.
      rewrite retr. rewrite sect. reflexivity.
  - exists f. split.
    + typeclasses eauto.
    + intros x. unfold compose.
    rewrite sect. rewrite retr. reflexivity. Defined.

#[export] Instance is_trans_equiv_types_eq : IsTrans _~=_.
Proof.
  intros A B C [f0 [[g0 IR0] [h0 IS0]]] [f1 [[g1 IR1] [h1 IS1]]].
  exists (f1 o f0). split.
  - exists (g0 o g1). split.
    + typeclasses eauto.
    + intros y. unfold compose.
    rewrite retr. rewrite retr. reflexivity.
  - exists (h0 o h1). split.
    + typeclasses eauto.
    + intros y. unfold compose.
    rewrite sect. rewrite sect. reflexivity. Defined.

Lemma transport_equiv (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) : P x ~= P y.
Proof.
  exists (transport P e). split.
  (* - intros a b f. apply f_equal. apply f. *)
  - exists (transport P (e ^-1)). split.
    + typeclasses eauto.
    + intros a. apply rew_opp_l.
  - exists (transport P (e ^-1)). split.
    + typeclasses eauto.
    + intros a. apply rew_opp_r. Defined.

End End.

Module Begin.

#[local] Notation "'_~=_'" := (fun A B : Type => IsEquivTypes' A B _=_ _=_).
#[local] Notation "A '~=' B" := (IsEquivTypes' A B _=_ _=_).

#[local] Lemma IP (A : Type) : IsProper (A := A -> A) (_=_ ==> _=_) id.
Proof. intros x y e. apply e. Defined.

(** TODO Investigate this implicit argument expansion. *)

Arguments IP {_} [_ _] _.

#[local] Lemma IR (A : Type) : IsRetr (A := A) _=_ id id.
Proof. intros x. apply eq_refl. Defined.

#[local] Lemma IS (A : Type) : IsSect (A := A) _=_ id id.
Proof. intros x. apply eq_refl. Defined.

#[export] Instance is_half_adjoint_id (A : Type) :
  IsCohIso (A := A) (B := A) _=_ _=_ id id (fun _ : A => _=_).
Proof.
  apply (Build_IsCohIso (fun _ : A => _=_) (Build_IsIso
  (Build_IsIsoL _=_ id id (@IP A) IR)
  (Build_IsIsoR _=_ id id (@IP A) IS))).
  intros x. apply eq_refl. Defined.

#[export] Instance is_refl_equiv_types_eq : IsRefl _~=_.
Proof. intros A. exists id, id. apply is_half_adjoint_id. Defined.

#[export] Instance is_sym_equiv_types_eq : IsSym _~=_.
Proof.
Admitted.

#[export] Instance is_trans_equiv_types_eq : IsTrans _~=_.
Proof.
Admitted.

Section Context.

Context (A : Type).

#[export] Instance is_retr_id :
  IsRetr (A := A) (B := A) _=_ id id.
Proof. intros x. apply eq_refl. Defined.

#[export] Instance is_sect_id :
  IsSect (A := A) (B := A) _=_ id id.
Proof. intros x. apply eq_refl. Defined.

#[export] Instance is_bi_inv_id :
  IsBiInv (A := A) (B := A) _=_ _=_ id.
Proof.
  split.
  - exists id. split; typeclasses eauto.
  - exists id. split; typeclasses eauto. Defined.

(* #[export] Instance is_equiv_types_eq : A ~= A.
Proof. exists id. apply is_bi_inv_id. Defined. *)

#[export] Instance is_equiv_types_eq : A ~= A.
Proof. exists id, id. apply is_half_adjoint_id. Defined.

End Context.

(** Equal types are equivalent. *)

#[export] Instance properer (A B : Type) (e : A = B) :
  IsProper (_=_ ==> _=_) (transport id e).
Proof.
  intros x y a.
  apply (transport (fun z : A => transport id e x = transport id e z) a).
  apply eq_refl. Defined.

Arguments properer {_ _} _ [_ _] _.

#[local] Open Scope type_scope.

(** These definitions are from the HoTT library,
    just to see if they work in this setting. *)

Definition concat_pV {A : Type}
  {x y : A} (p : x = y) : p ^-1 o p = id :=
  match p with id => id end.

Definition concat_Vp {A : Type}
  {x y : A} (p : x = y) : p o p ^-1 = id :=
  match p with id => id end.

Definition transport_pp {A : Type} (P : A -> Type)
  {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  transport _ (q o p) u = transport _ q (transport _ p u) :=
  match q with
  | id =>
      match p with
      | id => id
      end
  end.

Definition transport_pV {A : Type} (P : A -> Type)
  {x y : A} (p : x = y) (z : P y) :
  transport _ p (transport _ (p ^-1) z) = z :=
  f_equal (fun r : y = y => transport P r z) (concat_Vp p) o
  (transport_pp P (p ^-1) p z) ^-1.

Definition transport_Vp {A : Type} (P : A -> Type)
  {x y : A} (p : x = y) (z : P x) : transport _ (p ^-1) (transport _ p z) = z
  := f_equal (fun r : _ = _ => transport P r z) (concat_pV p) o
  (transport_pp P p (p ^-1) z) ^-1.

Definition transport2 {A : Type} (P : A -> Type)
  {x y : A} {p q : x = y} (r : p = q) (z : P x) :
  transport _ p z = transport _ q z :=
  f_equal (fun s : x = y => transport _ s z) r.

#[export] Instance idpather (A B : Type) (e : A = B) :
  IsCohIso _=_ _=_
  (transport id%core e) (transport id%core (e ^-1))
  (fun _ : _ => _=_).
Proof.
  (*
  apply (Build_IsCohIso (X := _=_) (Y := _=_)
  (transport id%core e) (transport id%core (e ^-1))
  (fun _ : _ => _=_)
  (properer e) (properer (e ^-1))
  (transport_Vp id%core e) (transport_pV id%core e)).
  intros x.
  unfold properer.
  epose proof (
  match e in _ = _ return
  transport2 id%core (concat_Vp e) (transport id%core e x) o
  transport_pp id%core (e ^-1) e (transport id%core e x) ^-1 =
  f_equal (transport id%core e)
  (transport2 id%core (concat_pV e) x o
  transport_pp id%core e (e ^-1) x ^-1) with
  | id => id
  end).
  *)
Admitted.

#[export] Instance idpathy (A B : Type) (e : A = B) :
  IsHAE _=_ _=_ (transport (fun C : Type => C) e).
Proof. exists (transport (fun C : Type => C) (e ^-1)). apply idpather. Defined.

Lemma transport_equiv (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) : P x ~= P y.
Proof.
  exists (transport P e), (transport P (e ^-1)). Admitted.

#[export] Instance idtoeqv (A B : Type) (a : A = B) : A ~= B.
Proof. apply (transport (_~=_ A) a). apply is_equiv_types_eq. Defined.

End Begin.

#[local] Notation "'_~=_'" := (fun A B : Type => IsEquivTypes A B _=_ _=_).
#[local] Notation "A '~=' B" := (IsEquivTypes A B _=_ _=_).

(** ** Proposition Extensionality *)

Class IsPropExt : Prop :=
  prop_ext (A B : Prop) (a : A <-> B) : A = B.

(** This lemma gets its name from [ZifyClasses.eq_iff]. *)

Lemma eq_iff (A B : Prop) (a : A = B) : A <-> B.
Proof. induction a. reflexivity. Qed.

(** ** Proposition Extensionality for Types *)

Class IsPropExtType : Prop :=
  prop_ext_type (A B : Type) `{!IsProp A} `{!IsProp B}
  (a : (A -> B) * (B -> A)) : A = B.

Lemma eq_iff_type (A B : Type) `{!IsProp A} `{!IsProp B}
  (a : A = B) : (A -> B) * (B -> A).
Proof. induction a. split; apply id. Defined.

(** ** Predicate Extensionality *)

Class IsPredExt : Prop :=
  pred_ext (A : Type) (P Q : A -> Prop) (a : forall x : A, P x <-> Q x) : P = Q.

(** ** Predicate Extensionality Axiom *)

Axiom predicate_extensionality :
  forall (A : Type) (P Q : A -> Prop) (a : forall x : A, P x <-> Q x),
  P = Q.

(** ** Function Extensionality *)

Class IsFunExt : Prop :=
  fun_ext (A B : Type) (f g : A -> B) (a : forall x : A, f x = g x) : f = g.

(** This lemma gets its name from [FunctionalExtensionality.equal_f]. *)

Lemma equal_f (A B : Type) (f g : A -> B) (a : f = g) (x : A) : f x = g x.
Proof. induction a. reflexivity. Qed.

(** ** Dependent Function Extensionality *)

Class IsFunExtDep : Prop :=
  fun_ext_dep (A : Type) (P : A -> Type)
  (f g : forall x : A, P x) (a : forall x : A, f x = g x) : f = g.

(** Dependent function extensionality implies function extensionality. *)

#[export] Instance fun_ext_dep_is_fun_ext
  `{!IsFunExtDep} : IsFunExt.
Proof. intros A B f g a. apply fun_ext_dep. intros x. apply a. Qed.

(** ** Type Extensionality *)

Class IsTypeExt : Prop :=
  type_ext (A B : Type) (f : A -> B) (g : B -> A)
  (r : forall x : A, g (f x) = x) (s : forall y : B, f (g y) = y) :
  A = B.

(** ** Type Extensionality Axiom *)

Axiom type_extensionality : forall (A B : Type)
 (f : A -> B) (g : B -> A)
 (r : forall x : A, g (f x) = x) (s : forall y : B, f (g y) = y),
 A = B.

(** ** Univalence *)

Class IsUniv : Prop :=
  uam (A B : Type) `{!A ~= B} : A = B.

(** ** Univalence Axiom *)

Axiom univalence : forall A B : Type,
  IsBiInv _=_ _=_ (End.idtoeqv (A := A) (B := B)).

Axiom univalence' : forall A B : Type,
  IsHAE _=_ _=_ (Begin.idtoeqv (A := A) (B := B)).

(** This is axiom 2.10.3 and its corollaries from the book. *)

Corollary ua_equiv (A B : Type) : (A = B) ~= (A ~= B).
Proof. exists End.idtoeqv. apply univalence. Defined.

Lemma ua (A B : Type) `{!A ~= B} : A = B.
Proof.
  pose proof equiv_types_bi_inv A B _=_ _=_ as IET.
  pose proof univalence A B as IBI.
  pose proof l_inv_iso_l as ILI.
  pose proof ex_proj1 ILI as e.
  apply e. apply IET. Defined.

Arguments ua {_ _} _.

(** Propositional extensionality
    makes functional extensionality an equality. *)

Lemma prop_fun_ext_dep `{IsPropExt} `{IsFunExtDep}
  (A : Type) (P : A -> Type) (f g : forall x : A, P x) :
  (forall x : A, f x = g x) = (f = g).
Proof.
  apply prop_ext. split.
  - intros a. apply fun_ext_dep. intros x. apply a.
  - intros a x. apply equal_f_dep. apply a. Qed.

(** Families of propositions are propositions. *)

Lemma eq_pi_is_prop `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsProp (P x)} : IsProp (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsProp _ |- _ => rename h into p
  end.
  intros g h. apply fun_ext_dep. intros x. apply p. Qed.

(** Families of contractible types are contractible. *)

Lemma eq_pi_is_contr `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsContr (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsContr _ |- _ => rename h into c
  end.
  apply @inhabited_prop_is_contr.
  - intros x. apply c.
  - apply (@eq_pi_is_prop _). intros x. apply contr_is_prop. Qed.

Module HomotopyTypicalDigression.

#[local] Open Scope ex_scope.
#[local] Open Scope sig_scope.

Class IsRetrType (A B : Type) (X : A -> A -> Prop) : Prop :=
  retr_type : exists (f : A -> B) (g : B -> A), IsRetr X f g.

Arguments IsRetrType _ _ _ : clear implicits.

(** This is lemma 3.11.7 from the book. *)

Lemma ret (A B : Type) `{!IsRetrType B A _=_}
  `{!IsContr A} : IsContr B.
Proof.
  destruct IsRetrType0 as [f [g IR]]. destruct contr as [x h].
  exists (g x). intros y. rewrite <- (retr (f := f) y). f_equal. apply h. Qed.

(** This was definition 4.2.4 from the book. *)

Definition cf (A : Type) (P : A -> Prop) (x : A)
  (s : {a : {x : A | P x} | proj1_sig a = x}) : P x.
Proof. destruct s as [[y a] e]. simpl in e. induction e. apply a. Defined.

Definition cg (A : Type) (P : A -> Prop) (x : A)
  (a : P x) : {a : {x : A | P x} | proj1_sig a = x}.
Proof. exists (x; a). reflexivity. Defined.

Lemma classes (A : Type) (P : A -> Prop) (x : A) :
  IsIso _=_ _=_ cf (cg P x).
Proof.
  split.
  - split.
    + typeclasses eauto.
    + intros [[y a] e]. simpl in e. unfold cf, cg. rewrite <- e. reflexivity.
  - split.
    + typeclasses eauto.
    + intros a. unfold cf, cg. reflexivity. Qed.

(** This is lemma 4.8.1 from the book. *)

Lemma classifier (A : Type) (P : A -> Prop) (x : A) :
  IsEquivTypes (fib _=_ (proj1_sig (P := P)) x) (P x) _=_ _=_.
Proof. exists cf. split; exists (cg P x); apply classes. Qed.

Lemma classifier' (A : Type) (P : A -> Prop) (x : A) :
  IsEquivTypes' (fib _=_ (proj1_sig (P := P)) x) (P x) _=_ _=_.
Proof. exists cf, (cg P x). eapply (Build_IsCohIso). Abort.

Import End.

#[local] Open Scope ex_scope.

Lemma ua_elim (A B : Type) (e : A = B) :
  idtoeqv e = (transport id e; is_bi_inv_eq_transport_id e).
Proof. reflexivity. Defined.

Lemma ua_comp (A B : Type) `{e : !A ~= B} (x : A) :
  applicate (idtoeqv (ua e)) x = applicate e x.
Proof.
  unfold ua, idtoeqv, applicate.
  unfold equiv_types_bi_inv.
  destruct (univalence A B) as [[g IIL] [h IIR]] eqn : u.
  destruct e as [f IBI] eqn : v. cbv.
  destruct (g e) as [].
Admitted.

Lemma ua_comp' (A B : Type) `{e : !A ~= B} :
  idtoeqv (ua e) = e.
Proof.
  unfold ua, End.idtoeqv.
  destruct (univalence A B) as [[g IIL] [h IIR]].
Admitted.

Lemma ua_uniq (A B : Type) (e : A = B) :
  ua (idtoeqv e) = e.
Proof. Admitted.

Lemma ua_refl (A : Type) :
  ua (refl (Reflexive := is_refl_equiv_types_eq) A) =
  @eq_refl Type A.
Proof. Admitted.

(*
Lemma eq_trans (A : Type) (x y z : A) (e : x = y) (f : y = z) : x = z.
Proof. induction e using eq_rect. induction f using eq_rect. apply eq_refl. Defined.
*)

Lemma ua_trans (A B C : Type) (e : A ~= B) (f : B ~= C) :
  ua (trans (Transitive := @is_trans_equiv_types_eq) A B C e f) =
  @eq_trans Type A B C (ua e) (ua f).
Proof.
  set (p := ua e). set (q := ua f).
  set (r := (eq_trans p q)%type).
  rewrite <- (ua_uniq r).
  unfold p, q in r.
Admitted.

Lemma ua_sym (A B : Type) (e : A ~= B) :
  ua (sym (Symmetric := @is_sym_equiv_types_eq) A B e) =
  @eq_sym Type A B (ua e).
Proof. Admitted.

(** This is lemma 4.9.2 from the book. *)

Lemma easy `{IsUniv} (A B X : Type)
  `{!A ~= B} : (X -> A) ~= (X -> B).
(** The form of this proof matters a lot. *)
Proof.
  epose proof ua _ as e.
  apply End.idtoeqv.
  induction e.
  reflexivity. Defined.

Definition inj1_sig (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} (x : A) : {x : A | P x} :=
  (x; ex_proj1 contr).

Lemma what (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsRetr _=_ proj1_sig inj1_sig.
Proof.
  intros [x a]. unfold proj1_sig, inj1_sig. f_equal.
  pose proof ex_proj2 contr a as b. apply b. Qed.

Lemma what' (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsSect _=_ proj1_sig inj1_sig.
Proof. intros x. unfold proj1_sig, inj1_sig. reflexivity. Qed.

(** This is corollary 4.9.3 from the book. *)

Lemma how (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} :
  IsBiInv _=_ _=_ (proj1_sig (P := P)).
Proof. split; exists inj1_sig; split;
  try typeclasses eauto; apply what || apply what'. Qed.

Lemma why (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} :
  {x : A | P x} ~= A.
Proof. exists proj1_sig. apply how. Qed.

(** This is theorem 4.9.4 from the book. *)

Lemma eq_pi_is_contr' `{IsUniv} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsContr (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsContr _ |- _ => rename h into c
  end.
  (** This requires things to be more transparent than is reasonable. *)
  pose proof what as a'.
  pose proof what' as a''.
  pose how as a; cbv beta in a.
  pose why as b; cbv beta in b.
  pose (easy (A := {x : A | P x}) (B := A) A) as IETsig.
  unfold easy in IETsig. subst a.
  destruct IETsig as [alpha [beta II]] eqn : e. subst IETsig.
  epose proof ret (B := forall x : A, P x) (A := fib _=_ alpha id) as IC.
  apply IC. Unshelve. hnf.
  - eset (phi (f : forall x : A, P x) := _ : fib _=_ alpha id%core).
    eset (psi (gp : fib _=_ alpha id%core) := _ : forall x : A, P x).
    exists phi, psi. unfold phi, psi. clear phi psi.
    intros h. admit.
  - hnf. pose proof how as z. destruct z as [f II'].
    admit.
Admitted.

(** This is theorem 4.9.5 from the book. *)

Lemma fun_now `{IsUniv} : IsFunExtDep.
Proof.
  intros A P f g a. epose proof eq_pi_is_contr'.
  epose proof ua as u. Admitted.

End HomotopyTypicalDigression.

(** Families of sets are sets. *)

Lemma eq_pi_is_set `{IsPropExt} `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsSet (P x)} : IsSet (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsSet _ |- _ => rename h into s
  end.
  intros f g.
  pose proof prop_fun_ext_dep f g as t. rewrite <- t. clear t.
  apply (@eq_pi_is_prop _).
  intros x. apply @set_is_prop_eq. apply s. Qed.

(** Fibrations are at the same homotopy level as their fibers. *)

Lemma eq_h_level_is_h_level `{IsPropExt} `{IsFunExtDep}
  (A : Type) (P : A -> Prop) (n : nat)
  `{!forall x : A, IsHLevel n (P x)} : IsHLevel n (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsHLevel _ _ |- _ => rename h into a
  end.
  revert A P a. induction n as [| p b]; intros A P a.
  - apply @contr_is_h_level_0. apply (@eq_pi_is_contr _).
    intros x. apply @h_level_0_is_contr. apply a.
  - intros f g.
    pose proof prop_fun_ext_dep f g as t. rewrite <- t. clear t.
    apply b. intros x. apply h_level_S_is_h_level_eq. apply a. Qed.

Module FromAxioms.

#[export] Instance is_proof_irrel : IsProofIrrel.
Proof. intros A B. apply proof_irrelevance. Qed.

#[export] Instance is_prop_ext : IsPropExt.
Proof. intros A B. apply propositional_extensionality. Qed.

#[export] Instance is_prop_ext_type : IsPropExtType.
Proof.
  intros A B IPA IPB [f g]. pose proof univalence A B as s.
  destruct s as [ua [IPidtoeqv IPua]]. apply ua. exists f. split.
  - exists g. split; try typeclasses eauto. intros x. apply irrel.
  - exists g. split; try typeclasses eauto. intros x. apply irrel. Qed.

#[export] Instance is_pred_ext : IsPredExt.
Proof. intros A P Q. apply predicate_extensionality. Qed.

#[export] Instance is_fun_ext : IsFunExt.
Proof. intros A B. apply functional_extensionality. Qed.

#[export] Instance is_fun_ext_dep : IsFunExtDep.
Proof. intros A P. apply functional_extensionality_dep. Qed.

#[export] Instance is_univ : IsUniv.
Proof. intros A B. apply univalence. Qed.

End FromAxioms.
