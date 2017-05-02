(*
 * Syntax and semantics for LTL
 * As well as some stream stuff
 * This is all based on "Fast LTL To Buechi Automata Translation" *)
Require Import ACE.
Require Import Paco.paco.
(* LProp is our type of propositional variables.
   They should be pointed and decidable. *)
(* TODO: fix the naming *)
Variable LProp : Type.
Variable lpoint : LProp.
Variable ldec :
  LProp -> LProp -> Cobool.
(* (* should this be if or iff? *)
Hypothesis ldec_correct :
forall a b, ldec a b = true <-> a = b *)
(* our states *)
Variable LState : Type.
(* denotation *)
Variable lsd : LState -> LProp -> Cobool.
Variable lseq : LState -> LState -> Cobool.
Variable lseq_correct :
  forall l1 l2,
    Coeq (lseq l1 l2) ctrue <-> (forall lp : LProp, Coeq (lsd l1 lp) (lsd l2 lp)).

(* LTL formulae *)
Inductive LTLF : Type :=
| Lp : LProp -> LTLF
| Lnot : LTLF -> LTLF
| Lor : LTLF -> LTLF -> LTLF
| LX : LTLF -> LTLF
(* weak until *)
| LW : LTLF -> LTLF -> LTLF
(* | LU : LTLF -> LTLF -> LTLF
| LR : LTLF -> LTLF -> LTLF  *)
.

Definition Ltt := Lor (Lp lpoint) (Lnot (Lp lpoint)).
Definition Lff := Lnot Ltt.
Definition Land (a b : LTLF) := Lnot (Lor (Lnot a) (Lnot b)).

(* additional temporal operators *)
Definition LR (a b : LTLF) :=
  LW a (Land a b).
(* Definition LR (a b : LTLF) :=
  Lnot (LU (Lnot a) (Lnot b)). *)
Definition LU (a b : LTLF) :=
  Lnot (LR (Lnot a) (Lnot b)).
Definition LF (a : LTLF) :=
  LU Ltt a.
Definition LG (a : LTLF) :=
  LR Lff a.

Definition sh {T : Type} (s : Stream T) :=
  match s with
  | scons h _ => h
  end.
Definition st {T : Type} (s : Stream T) :=
  match s with
  | scons _ t => t
  end.

(* Some stream utilities, based on
 https://github.com/gmalecha/coq-temporal/blob/master/theories/DiscreteStream.v *)

(* NB these aren't really that helpful, hard to use
   with coinduction in the way we would like *)
Definition candb (a b : Cobool) : Cobool :=
  match a, b with
  | ctrue, ctrue => ctrue
  | _, _ => cfalse
  end.

Definition cnotb (a : Cobool) : Cobool :=
  match a with
  | ctrue => cfalse
  | cfalse => ctrue
  end.

Definition tocbool (b : bool) : Cobool :=
  match b with
  | true => ctrue
  | false => cfalse
  end.

(* Q: Do we want state equality to be decidable?
   This seems like an additional assumption and is non obvious
 *)
(*
CoFixpoint Seq_dec (a b : Str) : cobool :=
  match a, b with
  | scons _ ah a', scons _ bh b' =>
    candb (tocbool (ldec ah bh)) (Seq_dec a' b')
  end.
 *)
(*
CoInductive StreamNeq : Str -> Str -> Prop :=
| NEqNow : forall ah bh,
    lsneq ah bh ->
    forall a b, StreamNeq (sc ah a) (sc bh b)
| NEqLater : forall ah bh,
    lseq ah bh -> (* TODO - need this one? *)
    forall a b, StreamNeq a b -> StreamNeq (sc ah a) (sc bh b).
*)
Ltac isc x := inversion x; subst; clear x.


(*
Lemma StreamEq_sane :
  forall a b, StreamEq a b -> StreamNeq a b ->
         forall b c, StreamEq b c. 
Proof.
  cofix.
  intros.
  isc H.
  isc H0.
  { unfold lseq, lsneq in *. congruence.
  inversion H.
  destruct H.
  inversion H0
  destruct H0.
  { inversion H0.
    constructor.
  apply (StreamEq_sane _ _ H H0 _ _).
Qed.
*)

(* LTLE is our evaluation relation
   LTLE' means that it evaluates to false
 *)

Definition Str := Stream LState.

CoInductive LTLE : LTLF -> Str -> Prop :=
| LEp : forall p s st, lsd s p = ctrue -> LTLE (Lp p) (scons s st)
| LEnot : forall f st, LTLE' f st -> LTLE (Lnot f) st
| LEor1 : forall f1 f2 st, LTLE f1 st -> LTLE (Lor f1 f2) st
| LEor2 : forall f1 f2 st, LTLE f2 st -> LTLE (Lor f1 f2) st
| LEX : forall f h st,
    LTLE f st -> LTLE (LX f) (scons h st)
| LEW1 : forall f1 f2 h st,
    LTLE f1 (scons h st) ->
    LTLE (LW f1 f2) st ->
    LTLE (LW f1 f2) (scons h st)
| LEW2 : forall f1 f2 st,
    LTLE f2 st ->
    LTLE (LW f1 f2) st
(*
| LEUlater : forall f1 f2 h st,
    LTLE f1 (sc h st) ->
    LTLE (LU f1 f2) st ->
    LTLE (LU f1 f2) (sc h st)
| LEUnow : forall f1 f2 h st,
    LTLE f2 (sc h st) ->
    LTLE (LG f2) st ->
    LTLE (LU f1 f2) (sc h st)
| LERlater : forall f1 f2 h st,
    LTLE f2 (sc h st) ->
    LTLE (LR f1 f2) st ->
    LTLE (LR f1 f2) (sc h st)
| LERnow : forall f1 f2 st,
    LTLE f1 st ->
    LTLE (LR f1 f2) st
*)
    with LTLE' : LTLF -> Str -> Prop :=
| LEp' : forall p s st, lsd s p = cfalse -> LTLE' (Lp p) (scons s st)
| LEnot' : forall f st, LTLE f st -> LTLE' (Lnot f) st
| LEor' : forall f1 f2 st, LTLE' f1 st -> LTLE' f2 st -> LTLE' (Lor f1 f2) st
| LEX' : forall f h t,
    LTLE' f t -> LTLE' (LX f) (scons h t)
(* How we can fail, option 1: neither holds *)
| LEW'1 : forall f1 f2 st,
    LTLE' f1 st -> LTLE' f2 st -> LTLE' (LW f1 f2) st
| LEW'2 : forall f1 f2 h st,
    LTLE f1 (scons h st) -> LTLE' (LW f1 f2) st -> LTLE' (LW f1 f2) (scons h st)
.
  Inductive even : nat -> Prop :=
  | zero_even : even 0
  | next_even : forall n, odd n -> even (S n)
  with odd : nat -> Prop :=
       | next_odd : forall n, even n -> odd (S n).

  Print even_ind.

  Inductive Conat : Set :=
  | CZ : Conat
  | CS : Conat -> Conat.

  CoInductive Coeven : nat -> Prop :=
  | zero_coeven : Coeven 0
  | next_coeven : forall n, Coodd n -> Coeven (S n)
  with Coodd : nat -> Prop :=
       | next_coodd : forall n, Coeven n -> Coodd (S n).

  Lemma boom : forall n, even n -> even (S (S n)).
    induction n.
    admit.
    intros.
    destruct H.
    admit.
    Admitted.

  Print even_ind.
  (* should this be odd (S n) -> P n
     or odd n -> P (S n)
   *)

  Definition cpred (n : Conat) : Conat :=
    match n with
    | CZ => CZ
    | CS n' => n'
    end.

  Section Coeven_coind.
    Variable P : nat -> Prop.

    (* I believe these are not the correct hypotheses *)
    Variable f : P 0.
    Variable f0 : forall n, Coodd n -> P (S n).

    Lemma Coeven_coind :
      forall n, P n ->
           Coeven n.
      cofix.
      intros.
      destruct n.
      { constructor. }
      { 

        apply Coeven_coind. Guarded.

        right.
        specialize (f0 (CS n)).
        destruct n.
        admit.

        Guarded.
        specialize (Coeven_coind (CS (CS n)) H).
        simpl in Coeven_coind.
        destruct Coeven_coind.
        inversion e.
        apply c.
        Guarded.
        specialize (ident term+)
        Guarded.
        auto.
        eapply Coeven_coind.
        apply Coeven_coind


Section LTLE_coind.
  Variable R : LTLF -> Str -> Prop.
  Variable R' : LTLF -> Str -> Prop.
  Print LTLF.

  Hypothesis LEpCase :
    forall p s,
      R (Lp p) s -> lsd (shd s) p = ctrue.
  Hypothesis LEnotCase :
    forall f s,
      R (Lnot f) s -> R' f s.
  Hypothesis LEorCase :
    forall f1 f2 s,
      R (Lor f1 f2) s -> (R f1 s \/ R f2 s).
  Hypothesis LEXCase :
    forall f1 s,
      R (LX f1) s -> R f1 (stl s).
  Hypothesis LEWCase :
    forall f1 f2 s,
      R (LW f1 f2) s ->
      ((R f1 s /\ R (LW f1 f2) (stl s))
       \/ R f2 s).

  Hypothesis LEpCase' :
    forall p s,
      R' (Lp p) s -> lsd (shd s) p = cfalse.
  Hypothesis LEnotCase' :
    forall f s,
      R' (Lnot f) s -> R f s.
  Hypothesis LEorCase' :
    forall f1 f2 s,
      R' (Lor f1 f2) s ->
      (R' f1 s /\ R' f2 s).
  Hypothesis LEXCase' :
    forall f1 s,
      R' (LX f1) s -> R' f1 (stl s).

  (* just need to do this one, then on to the coinduction principle *)
  Hypothesis LEWCase' :
    forall f1 f2 s,
      R' (LW f1 f2) s ->
      ((LTLE' f1 s /\ LTLE' f2 s) \/
       (LTLE f1 s /\ LTLE' (LW f1 f2) s)).

  (* TODO: do we also need one for LTLE'? *)
  (* YES, we do. *)
  Lemma LTLE_coind :
    forall f s, (Coand (R f s -> LTLE f s) (R' f s -> LTLE' f s)).
  Proof.
    cofix; intros; destruct f.
    { split; intros.
      destruct s.
      econstructor.
      eapply LEpCase.
    intros.
    destruct f.
    split; intros.
    { destruct f; intros.
      Print LTLE.
      Guarded.
      {
    constructor.

End LTLE_coind.

Lemma LTLE_false :
  forall st,
    LTLE Lff st ->
    False.
Proof.
  inversion 1; subst. clear H.
  inversion H1; subst; clear H1.
  inversion H2; subst; clear H2.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  congruence.
Qed.

Ltac fwd :=
  repeat match goal with
         | H : Coand _ _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
  end.

(*
Lemma LG_now :
  forall p st,
    LTLE (LG p) st ->
    LTLE p st.
Proof.
  intros.
  isc H.
  { unfold Lff in H2. isc H2. isc H0. assumption. }
  { apply LTLE_false in H3. contradiction. }
Qed.
 *)

Lemma LTLE_Strcmp :
  forall f st st',
    Strcmp Coeq st st' ->
    Agree f st st'.
Proof.
  cofix.
  induction f.
  Focus 5.
  intros.
  constructor.
  { intros.
    isc H0.
    { 
      specialize (LTLE_Strcmp (LW f1 f2)).
      isc H.
      specialize (LTLE_Strcmp _ _ H6).
      destruct LTLE_Strcmp as [HS1  HS2].
      apply LEW1.
      { admit. }
      { apply HS1. auto. }
    }
    Guarded.


      Guarded.
    }
    Focus 2.
    apply LEW2.

    iscspecialize (LTLE_Strcmp f1 st st'). intros. isc H0.
    { 

      specialize (IHf1 _ _ H).
      isc IHf1.
  isc H.
  constructor.
  eapply 
  intros.
  constructor.
  eapply (Ag st0 st').
  Check Ag.
  isc H.

  eapply Ag.
Abort.

(*cofix.
  Print Strcmp.
  intros.
  destruct H.
*)

Lemma LTLE_Strcmp :
  forall f st st',
    Strcmp Coeq st st' -> Coand (LTLE f st -> LTLE f st') (LTLE' f st -> LTLE' f st').
Proof.
  intros.
  isc H.
  (*cofix.*)
  induction f.
  Focus 5.
  split; intros.



  { intros.
    split; intros.
    { isc H. isc H1. isc H0. constructor. assumption. }
    { isc H0. isc H. constructor. isc H3. assumption. } }
  { intros. split; intros.
    { isc H0. specialize (IHf _ _ H). destruct IHf.
      constructor. auto. }
    { isc H0. specialize (IHf _ _ H). destruct IHf. constructor. auto. } }
  { intros.
    split; intros.
    { isc H0.
      { apply LEor1. specialize (IHf1 _ _ H).
        destruct IHf1. auto. }
      { apply LEor2. specialize (IHf2 _ _ H).
        destruct IHf2. auto. } }
    { isc H0.
      { apply LEor'.
        { specialize (IHf1 _ _ H).
          destruct IHf1. auto. }
        { specialize (IHf2 _ _ H).
          destruct IHf2. auto. } } } }
  { intros. split; intros.
    { isc H0. isc H. constructor.
      specialize (IHf _ _ H5). destruct IHf. auto. }
    { isc H0. isc H. constructor.
      specialize (IHf _ _ H5). destruct IHf. auto. } }
  { intros.
    split; intros.
    { specialize (IHf1 _ _ H). specialize (IHf2 _ _ H).
      destruct IHf1; destruct IHf2.
      isc H0.
      { cofix. isc H. Guarded. isc H2.
        cofix.
        apply LEW1.
        { auto. }
        { 
          constructor.
        specialize (LTLE_Strcmp (LW f1 f2)). Guarded.
      apply l. auto. }
      Guarded.
      clear LTLE_Strcmp.
      Guarded.
      isc H.
      destruct IHf1; destruct IHf2.
      isc H0.
      { 

      apply LEW1.
      specializeisc H0.
      apply LTLE_Strcmp.
      Guarded.
      gv
      apply LEW1.
    Print LTLE.
    constructor.

    split; intros.
    { cofix.
      
      isc H0.
      {
      auto.
    }
 auo.
      {
        Print LTLE.
        constructor.

    {
      isc H2.
    isc H0. destruct st'. isc H. isc H4. econstructor; eauto. }
  { intros. isc H0. constructor.
    
    cofix.
    induction H2.
    
    isc H. isc H1.

  SearchAbout LTLEeapply IHf1.
      econstructor. econstructor. eapply H6. eassumption. }
    { isc H2.
      econstructor.
      econstructor.
  }
  [admit | admit | admit | admit|].
  generalize dependent f1. generalize dependent f2.
  cofix.
  intros.
  isc H0.
  { isc H. eapply LEW1.
    { isc H2. eapply IHf1.
      econstructor. econstructor. eapply H6. eassumption. }
    { isc H2.
      eapply LTLE_bisim. eapply IHf2. eapply IHf1.
      eapply H6. eapply H5. } }
  admit.
Admitted.
  econstructor.
      econstructor.
  }
Qed.
(* a fwd tactic would be helpful here too *)
Lemma LTLE_sanity :
  forall f st st', Strcmp Coeq st st' -> LTLE f st -> LTLE' f st' -> Cofalse.
Proof.
  induction f.
  admit.
  admit.
  admit.
  admit.

  cofix.
  intros.
  isc H0.
  { isc H1.
    { isc H.
      eapply IHf1.

  induction H0.
  intros.
  isc H0.
  { isc H1.
    { specialize (IHf1 _ _ H H4 H3). auto. }
    { specialize (IHf2 

  intros. isc H1. isc H. isc H0. congruence.
  intros.
  isc H1. isc H0.
  generalize (LTLE_eq'); intro Heq'.
  eapply IHf; eauto.
  Focus 6.
  intros.
  isc H1.
  { auto. }
  { apply IHLTLE; auto.


  induction f.
  { inversion 1; subst. inversion 1; congruence. }
  { inversion 1; subst. clear H. inversion 1; subst.
    apply (IHf st0); auto. }
  { inversion 1; subst;
      inversion 1; subst.
    { apply (IHf1 st0); auto. }
    { apply (IHf2 st0); auto. } }
  { inversion 1; subst; inversion 1; subst.
    apply (IHf st1); auto. }
  { intros.
    isc H0.
    { isc H.
      { eapply IHf1; eauto. }
      { eapply IHf2; eauto. } }
    { isc H.
      { isc H5.
        { isc H7.


          eapply IHf1; eauto.
          eapply IHf2; eauto. }
        { isc H7.
        



        }
        { isc H6. eapply IHf2; eauto. } }
        { isc H7.
          {

    induction H; subst.
    { intros. isc H0. congruence. }
    { intros. isc H0. eapply IHf1; eauto.

    isc H0. isc H4.
    { induction H. isc H.
      { isc H7.
      (* f1 U f2 holds now
         f2 doesn't hold now -> f1 must hold now *)
         

      isc H2. isc H5.
      {
      isc H.
      { isc H7.

      inversion H; suubs
    inversion H0; subst; clear H0.
    inversion H4; subst; clear H4.
    { inversion H; subst; clear H.
      { inversio
      inversion H5; subst; clear H5.
    { inversion H4; subst; clear H4.
      { inversion H7; subst; clear H7.
    { inversion H; subst.
      { eapply IHf1; eauto. }
      { eapply IHf2; eauto. } }
    { inversion H; subst.
      { eapply IHf1; eauto. }
      { (* do inversion on the resultant LGs *)
        inversion H5; subst.
    inversion 1; subst.
    { inversion 1; subst.
      { eapply IHf1; eauto. }
      { eapply IHf1; eauto. }
      { 

        specialize (IHf1 _ H2).
    inversion 1; subst.
    inversion H6. 
    inversion H8; subst.
    intros. 
    apply (IHf st0 _ _).
  intros.
  inversion 1.

Print LTLE_ind.

(* Now, we need our def of VWAA (v weak alternating automata) *)