(** * Extensionality and Univalence *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.ProofIrrelevance
  Logic.PropExtensionality Logic.PropExtensionalityFacts.
From DEZ.Is Require Export
  Irrelevant Isomorphic.

(** We declare various axiom schemes as classes
    in hopes of one day turning them into theorems. *)

Reserved Notation "x '~=' y" (no associativity, at level 70).

#[local] Notation "'_~=_'" := (fun A B : Type => IsEquivTypes A B _=_ _=_).
#[local] Notation "A '~=' B" := (IsEquivTypes A B _=_ _=_).

#[export] Instance is_refl_equiv_types_eq : IsRefl _~=_.
Proof. intros A. exists id. typeclasses eauto. Qed.

#[export] Instance is_sym_equiv_types_eq : IsSym _~=_.
Proof.
  intros A B [f [[g IR] [h IS]]]. exists (g o f o h). split.
  - exists f. intros y. unfold compose.
    rewrite retr. rewrite sect. reflexivity.
  - exists f. intros x. unfold compose.
    rewrite sect. rewrite retr. reflexivity. Qed.

#[export] Instance is_trans_equiv_types_eq : IsTrans _~=_.
Proof.
  intros A B C [f0 [[g0 IR0] [h0 IS0]]] [f1 [[g1 IR1] [h1 IS1]]].
  exists (f1 o f0). split.
  - exists (g0 o g1). intros y. unfold compose.
    rewrite retr. rewrite retr. reflexivity.
  - exists (h0 o h1). intros y. unfold compose.
    rewrite sect. rewrite sect. reflexivity. Qed.

Definition transport (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) (a : P x) : P y.
Proof. induction e. apply a. Defined.

Lemma transport_equiv (A : Type) (P : A -> Type)
  (x y : A) (e : x = y) : P x ~= P y.
Proof.
  exists (transport P e). split.
  (* - intros a b f. apply f_equal. apply f. *)
  - exists (transport P (e ^-1)). intros a. apply rew_opp_l.
  - exists (transport P (e ^-1)). intros a. apply rew_opp_r. Defined.

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

Section Context.

Context (A : Type).

#[export] Instance is_retr_id :
  IsRetr (A := A) (B := A) _=_ id id.
Proof. intros x. apply eq_refl. Defined.

#[export] Instance is_sect_id :
  IsSect (A := A) (B := A) _=_ id id.
Proof. intros x. apply eq_refl. Defined.

#[export] Instance is_equiv_fn_id :
  IsEquivFn (A := A) (B := A) _=_ _=_ id.
Proof.
  split.
  - exists id. apply is_retr_id.
  - exists id. apply is_sect_id. Defined.

#[export] Instance is_equiv_types_eq : A ~= A.
Proof. exists id. apply is_equiv_fn_id. Defined.

End Context.

(** Equal types are equivalent. *)

#[export] Instance idtoeqv (A B : Type) (a : A = B) : A ~= B.
Proof. apply (transport (_~=_ A) a). apply is_equiv_types_eq. Defined.

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

(** ** Univalence *)

Class IsUniv : Prop :=
  uam (A B : Type) `{!A ~= B} : A = B.

(** ** Univalence Axiom *)

Axiom univalence : forall A B : Type,
  IsEquivFn _=_ _=_ (idtoeqv (A := A) (B := B)).

(** This is axiom 2.10.3 and its corollaries from the book. *)

Corollary ua_equiv (A B : Type) : (A = B) ~= (A ~= B).
Proof. exists idtoeqv. apply univalence. Defined.

Lemma ua (A B : Type) `{!A ~= B} : A = B.
Proof.
  pose proof univalence A B as IEF.
  destruct IEF as [[g IR] [h IS]].
  apply g. typeclasses eauto. Defined.

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

(** This is definition 4.2.4 from the book. *)

Definition fib (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (y : B) : Type :=
  {x : A | X (f x) y}.

Equations IsContrFn (A B : Type) (f : A -> B) : Prop :=
  IsContrFn f := forall y : B, IsContr (fib _=_ f y).

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
  - typeclasses eauto.
  - typeclasses eauto.
  - intros [[y a] e]. simpl in e. unfold cf, cg. rewrite <- e. reflexivity.
  - intros a. unfold cf, cg. reflexivity. Qed.

(** This is lemma 4.8.1 from the book. *)

Lemma classifier (A : Type) (P : A -> Prop) (x : A) :
  IsEquivTypes (fib _=_ (proj1_sig (P := P)) x) (P x) _=_ _=_.
Proof. exists cf. split; exists (cg P x); apply classes. Qed.

Lemma ua_elim (A B : Type) (e : A = B) :
  idtoeqv e = transport_equiv id e.
Proof. Abort.

Lemma ua_comp (A B : Type) `{e : A ~= B} :
  idtoeqv (ua e) = e.
Proof.
  pose proof univalence A B as IEF.
  destruct IEF as [[g IR] [h IS]].
  destruct e as [f IEF]. unfold idtoeqv.
  set (a := ex_intro (fun f : A -> B => IsEquivFn _=_ _=_ f) f IEF).
  enough (rew [fun C : Type => A ~= C] ua a in is_equiv_types_eq A = a)
  by assumption. pose proof ua_equiv A B as IET. Admitted.

Lemma ua_uniq (A B : Type) (e : A = B) :
  ua (idtoeqv e) = e.
Proof. Admitted.

Lemma ua_univ (A B : Type) `{c : A ~= B} (e : A = B) :
  c = idtoeqv e.
Proof. unfold idtoeqv. Admitted.

(** This is lemma 4.9.2 from the book. *)

Lemma easy `{IsUniv} (A B X : Type)
  `{!IsEquivTypes A B _=_ _=_} : IsEquivTypes (X -> A) (X -> B) _=_ _=_.
(** The form of this proof matters a lot. *)
Proof.
  pose proof ua _ as e.
  apply idtoeqv.
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
  IsEquivFn _=_ _=_ (proj1_sig (P := P)).
Proof. split; exists inj1_sig; apply what || apply what'. Qed.

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
    Unshelve. 2: { exists (fun x => (x; f x)). admit. }
    eset (psi (gp : fib _=_ alpha id%core) := _ : forall x : A, P x).
    Unshelve. 2: { destruct gp as [g p]. intros x.
      pose (proj2_sig (g x)) as j. cbv beta in j.
      assert (j' : P (alpha g x)) by admit.
      pose proof equal_f p x as h. rewrite h in j'. apply j'. }
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
  - exists g. intros x. apply irrel.
  - exists g. intros x. apply irrel. Qed.

#[export] Instance is_pred_ext : IsPredExt.
Proof. intros A P Q. apply predicate_extensionality. Qed.

#[export] Instance is_fun_ext : IsFunExt.
Proof. intros A B. apply functional_extensionality. Qed.

#[export] Instance is_fun_ext_dep : IsFunExtDep.
Proof. intros A P. apply functional_extensionality_dep. Qed.

#[export] Instance is_univ : IsUniv.
Proof. intros A B. apply univalence. Qed.

End FromAxioms.
