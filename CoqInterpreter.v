(*Inductive nat : Set := | O : nat.*)

Inductive ope : nat -> nat -> Set :=
        | oz : ope O O
        | os : forall n m : nat, ope n m -> ope (S n) (S m)
        | o' : forall n m : nat, ope n m -> ope n (S m).

Lemma oi : forall n : nat, ope n n.
induction n.
  exact oz.
  eapply os.
    eapply IHn.
Defined.

Lemma oe : forall n : nat, ope O n.
induction n.
  exact oz.
  eapply o'.
    eapply IHn.
Defined.

Lemma oc' : forall n m : nat, ope n m ->
      forall p : nat, ope p n -> ope p m.
induction 1.
  intros.
    inversion H.
      eapply oz.
  intros.
    inversion H0.
      eapply os.
        eapply IHope.
          eapply H3.
      eapply o'.
        eapply IHope.
          eapply H3.
  intros.
    eapply o'.
      eapply IHope.
        eapply H0.
Defined.

Definition oc (p n m : nat)(th : ope p n)(ph : ope n m)
  : ope p m
  := oc' n m ph p th.

Inductive tm (n : nat) : Set :=
  | var : ope 1 n -> tm n
  | prop : tm n
  | type : nat -> tm n
  | pi : tm n -> tm (S n) -> tm n
  | lam : tm n -> tm (S n) -> tm n
  | app : tm n -> tm n -> tm n.

Inductive dir : Set := | chk | syn .

Inductive va (n : nat) : dir -> Set :=
  | vvar : ope 1 n -> va n syn
  | vapp : va n syn -> va n chk -> va n syn
  | vprop : va n chk
  | vtype : nat -> va n chk
  | vpi : va n chk ->
          forall m, (ope 1 m -> va n chk) ->
          tm (S m) -> va n chk
  | vlam : va n chk ->
          forall m, (ope 1 m -> va n chk) ->
          tm (S m) -> va n chk
  | vem : va n syn -> va n chk.

Inductive EVAL (X : Set) : Set :=
  | ret : X -> EVAL X
  | eva : forall n : nat, tm n ->
          forall m : nat, (ope 1 n -> va m chk) ->
          (va m chk -> EVAL X) -> EVAL X
  | nor : forall n : nat, va n chk ->
          (tm n -> EVAL X) -> EVAL X
  | err : EVAL X.

Lemma snoc : forall X : Set, forall n : nat,
             (ope 1 n -> X) -> X ->
             (ope 1 (S n) -> X).
intros X n xs x i.
  inversion i.
    exact x.
    exact (xs H1).
Defined.

Lemma appv : forall m : nat, va m chk -> va m chk ->
        EVAL (va m chk).
intros m f s.
  inversion f.
    eapply err. (* prop *)
    eapply err. (* type *)
    eapply err. (* pi *)
    eapply (eva _ (S m0) H1 m). (* lam *)
      eapply snoc.
        exact H0.
        exact s.
        intros t.
          eapply ret.
            exact t.
    eapply ret. (* stuck *)
      eapply vem.
        eapply vapp.
          exact H.
          exact s.
Defined.

Lemma bind : forall X Y : Set,
             EVAL X -> (X -> EVAL Y) -> EVAL Y.
intros X Y ex k.
  induction ex.
    exact (k x).
    eapply (eva _ n t m v).
      intros u.
        exact (H u).
    eapply (nor _ _ v). intros u. exact (H u).
    eapply err.
Defined.

Lemma eval : forall n : nat, tm n ->
             forall m : nat, (ope 1 n -> va m chk) ->
             EVAL (va m chk).
induction 1.
  intros m g. (* var *)
    eapply ret. 
      exact (g o).
  intros m g. (* prop *)
    eapply ret.
      eapply vprop.
  intros m g. (* type *)
    eapply ret.
      eapply vtype.
        exact n0.
  intros m g. (* pi *)
    eapply bind.
      eapply (IHtm1 _ g).
      intros S'.
        eapply ret.
          eapply vpi.
            exact S'.
            exact g.
            exact H0.
  intros m g. (* lam *)
    eapply bind.
      eapply (IHtm1 _ g).
      intros S'.
        eapply ret.
          eapply vlam.
            exact S'.
            exact g.
            exact H0.
  intros m g. (* app *)
    eapply bind. eapply (IHtm1 _ g). intros f.
      eapply bind. eapply (IHtm2 _ g). intros s.
        eapply appv.
          exact f.
          exact s.
Defined.

Lemma thinv : forall n : nat, forall d : dir, va n d ->
              forall m : nat, ope n m -> va m d.
induction 1.
  intros m th. (* vvar *)
    eapply vvar.
      eapply oc. exact o. exact th.
  intros m th. (* vapp *)
    eapply vapp. eapply (IHva1 _ th). eapply (IHva2 _ th).
  intros m th. (* vprop *)
    eapply vprop.
  intros m th. (* vtype *)
    eapply vtype. exact n0.
  intros m' th. (* vpi *)
    eapply vpi.
      eapply (IHva _ th).
      intros i. eapply (H0 i). exact th. exact t.
  intros m' th. (* vlam *)
    eapply vlam.
      eapply (IHva _ th).
      intros i. eapply (H0 i). exact th. exact t.
  intros m th. (* vem *)
    eapply vem.
      eapply (IHva _ th).
Defined.

Lemma norm : forall n : nat, forall d : dir,
             va n d -> EVAL (tm n).
induction 1.
  eapply ret. eapply var. exact o.
  eapply bind. exact IHva1. intros f.
    eapply bind. exact IHva2. intros s.
      eapply ret. eapply app. exact f. exact s.
  eapply ret. eapply prop.
  eapply ret. eapply type. exact n0.
  eapply bind. exact IHva. intros S'.
    eapply eva.
      exact t.
      eapply snoc.
        intros i. eapply thinv.
          eapply (v i).
          eapply o'. eapply oi.
        eapply vem. eapply vvar. eapply os. eapply oe.
      intros T. eapply nor. eapply T.
        intros T'. eapply ret. eapply pi.
          exact S'. exact T'.
  eapply bind. exact IHva. intros S'.
    eapply eva.
      exact t.
      eapply snoc.
        intros i. eapply thinv.
          eapply (v i).
          eapply o'. eapply oi.
        eapply vem. eapply vvar. eapply os. eapply oe.
      intros T. eapply nor. eapply T.
        intros T'. eapply ret. eapply lam.
          exact S'. exact T'.
  exact IHva.
Defined.

CoInductive Delay (T : Set) : Set :=
  | now : T -> Delay T
  | wait : Delay T -> Delay T
  | fail : Delay T.

Lemma run : forall X : Set, EVAL X -> Delay X.
cofix ru.
  destruct 1.
    eapply now. exact x.
    eapply wait. eapply ru.
      eapply bind.
        eapply eval. exact t. exact v.
        exact e.
    eapply wait. eapply ru.
      eapply bind.
        eapply norm. exact v.
        exact e.
    eapply fail.
Defined.

Lemma normalize : forall n : nat, tm n -> Delay (tm n).
intros n t.
  eapply run.
    eapply bind.
      eapply eval.
        eapply t.
        intros i. eapply vem. eapply vvar. exact i.
      intros v. eapply nor.
        exact v.
        eapply ret.
Defined.

Lemma PN : forall n : nat, tm n.
intros n.
  eapply pi.
    eapply prop.
    eapply pi.
      eapply pi.
        eapply var. eapply os. eapply oe.
        eapply var. eapply o'. eapply os. eapply oe.
      eapply pi.
        eapply var. eapply o'. eapply os. eapply oe.
        eapply var. eapply o'. eapply o'. eapply os. eapply oe.
Defined.

Lemma PZ : forall n : nat, tm n.
intros n.
  eapply lam.
    eapply prop.
    eapply lam.
      eapply pi.
        eapply var. eapply os. eapply oe.
        eapply var. eapply o'. eapply os. eapply oe.
      eapply lam.
        eapply var. eapply o'. eapply os. eapply oe.
        eapply var. eapply os. eapply oe.
Defined.

Lemma PS : forall n : nat, tm n.
intros n.
  eapply lam.
    eapply (PN n).
    eapply lam.
      eapply prop.
      eapply lam.
        eapply pi.
          eapply var. eapply os. eapply oe.
          eapply var. eapply o'. eapply os. eapply oe.
        eapply lam.
          eapply var. eapply o'. eapply os. eapply oe.
          eapply app.
            eapply var. eapply o'. eapply os. eapply oe.
            eapply app. eapply app. eapply app.
              eapply var. eapply o'. eapply o'. eapply o'. eapply os. eapply oe.
              eapply var. eapply o'. eapply o'. eapply os. eapply oe.
              eapply var. eapply o'. eapply os. eapply oe.
              eapply var. eapply os. eapply oe.
Defined.

Lemma P1 : forall n : nat, tm n.
intros n.
  eapply app.
    exact (PS n).
    exact (PZ n).
Defined.

Lemma gas : forall X : Set, forall n : nat, Delay X -> option X.
intros X n.
  induction n.
    intros d. eapply None.
    intros d. destruct d.
      eapply Some. exact x.
      eapply IHn. exact d.
      eapply None.
Defined.

Compute (gas _ 42 (normalize 0 (P1 0))).

Lemma P2 : forall n : nat, tm n.
intros n.
  eapply app.
    exact (PS n).
    exact (P1 n).
Defined.

Compute (gas _ 42 (normalize 0 (P2 0))).

Lemma P4 : forall n : nat, tm n.
intros n.
  eapply lam. eapply prop.
    eapply app. eapply app. eapply P2.
      eapply pi.
        eapply var. eapply os. eapply oe.
        eapply var. eapply o'. eapply os. eapply oe.
      eapply app.
        eapply P2.
        eapply var. eapply os. eapply oe.
Defined.

Compute (gas _ 420 (normalize 0 (P4 0))).
