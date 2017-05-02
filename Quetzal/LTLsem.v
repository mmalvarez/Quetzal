(*
 * Syntax and semantics for LTL
 * As well as some stream stuff
 * This is all based on "Fast LTL To Buechi Automata Translation" *)
(* LProp is our type of propositional variables.
   They should be pointed and decidable. *)
(* TODO: fix the naming *)
Variable LProp : Type.
Variable lpoint : LProp.
Variable ldec :
  LProp -> LProp -> bool.
(* (* should this be if or iff? *)
Hypothesis ldec_correct :
forall a b, ldec a b = true <-> a = b *)

(* our states; we need equality on them too *)
Variable LState : Type.
(* denotation *)
Variable lsd : LState -> LProp -> bool.

(* equality for states. (do we need decidability?) *)
Definition lseq (s1 s2 : LState) : Prop :=
  forall p, lsd s1 p = lsd s2 p.

(* Variable lsdec : LState -> LState -> bool. *)
(* Hypothesis LSdec_correct :
forall a b, lsdec a b = true <-> a = b.*)

(* LTL formulae *)
(* Q: should we have R as a primitive too? *)
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

CoInductive Stream (T : Type) :=
  | scons : T -> Stream T -> Stream T.

(* "smart" constructors *)
Definition Str := Stream LState.
Definition sc := scons LState.
Definition st (s : Str) :=
  match s with
  | scons _ _ t => t
  end.

(* Used to define until, but this is a bad way to do it! *)
Fixpoint snoc {T : Type} (x : T) (l : list T) : list T :=
  match l with
  | nil => cons x nil
  | cons h t => cons h (snoc x t)
  end.

Inductive StreamPref {T : Type} :
  Stream T -> list T -> Stream T -> Prop :=
| SpNil : forall s, StreamPref s nil s 
| SpCons : forall s (n : T) t s',
    StreamPref s t (scons T n s') ->
    StreamPref s (snoc n t) s'.

(* Some stream utilities, based on
 https://github.com/gmalecha/coq-temporal/blob/master/theories/DiscreteStream.v *)
(* should this be a decider also, or a relation? *)
CoInductive StreamEq : Str -> Str -> Prop :=
| SEq : forall ah a bh b,
    lseq ah bh ->
    StreamEq a b ->
    StreamEq (sc ah a) (sc bh b).

(*
CoInductive cobool : Set :=
| ctrue
| cfalse.

CoFixpoint str_dec (a : Str) (b : Str) : cobool :=
  match a with
  | scons _ _ _ => ctrue
  end
.
*)

(* LTLE is our evaluation relation
   LTLE' means that it evaluates to false
 *)

(* Q: Better to use Weak Until operator? *)
Inductive LTLE : LTLF -> Str -> Prop :=
| LEp : forall p s st, lsd s p = true -> LTLE (Lp p) (sc s st)
| LEnot : forall f st, LTLE' f st -> LTLE (Lnot f) st
| LEor1 : forall f1 f2 st, LTLE f1 st -> LTLE (Lor f1 f2) st
| LEor2 : forall f1 f2 st, LTLE f2 st -> LTLE (Lor f1 f2) st
| LEX : forall f h st,
    LTLE f st -> LTLE (LX f) (sc h st)
| LEW1 : forall f1 f2 h st,
    LTLE f1 (sc h st) ->
    LTLE (LW f1 f2) st ->
    LTLE (LW f1 f2) (sc h st)
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
| LEp' : forall p s st, lsd s p = false -> LTLE' (Lp p) (sc s st)
| LEnot' : forall f st, LTLE f st -> LTLE' (Lnot f) st
| LEor' : forall f1 f2 st, LTLE' f1 st -> LTLE' f2 st -> LTLE' (Lor f1 f2) st
| LEX' : forall f h t,
    LTLE' f t -> LTLE' (LX f) (sc h t)
(* How we can fail, option 1: neither holds *)
| LEW'1 : forall f1 f2 st,
    LTLE' f1 st -> LTLE' f2 st -> LTLE' (LW f1 f2) st
| LEW'2 : forall f1 f2 h st,
    LTLE f1 (sc h st) -> LTLE' (LW f1 f2) st -> LTLE' (LW f1 f2) (sc h st)
.
(* Option 3: f1 fails to hold, but f2 has not held yet *)
(*
| LEU' : forall f1 f2 st,
    LTLE (LR (Lnot f1) (Lnot f2)) st -> LTLE' (LU f1 f2) st
| LER' : forall f1 f2 st,
    LTLE (LU (Lnot f1) (Lnot f2)) st -> LTLE' (LR f1 f2) st
*)
(*
| LEUnow' : forall f1 f2 st,
    LTLE' f1 st -> LTLE' f2 st -> LTLE' (LU f1 f2) st
*)

(* TODO this one is wrong... *)
                                      (*
| LEUearly' : forall f1 f2 h st,
    LTLE' f1 (sc h st) ->
    LTLE' (LG f2) st ->
    LTLE' (LU f1 f2) (sc h st)
| LEUlate' : forall f1 f2 h st,
    LTLE' (LU f1 f2) st ->
    LTLE' f2 st ->
    LTLE' (LU f1 f2) (sc h st)
| LEUfuture' : forall f1 f2 h st,
      LTLE' (LG f2) st ->
      LTLE' (LU f1 f2) st ->
      LTLE' (LU f1 f2) (sc h st)
*)
(*
| LEUlater' : forall f1 f2 h st,
    LTLE f1 (sc h st) ->
    LTLE' (LU f1 f2) st ->
    LTLE' (LU f1 f2) (sc h st)
| LEUnow' : forall f1 f2 h st,
    LTLE' f1 st ->
    LTLE' (LG f2) st ->
    LTLE' (LU f1 f2) st
*)

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

Ltac isc x := inversion x; subst; clear x.

Ltac fwd :=
  repeat match goal with
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

(* a fwd tactic would be helpful here too *)

(* Do we need to strengthen the induction hypothesis to include not cases *)
Lemma LTLE_eq' :
  forall f s1 s2,
    StreamEq s1 s2 ->
    ((LTLE f s1 -> LTLE f s2) /\ (LTLE f s2 -> LTLE f s1)
     /\(LTLE' f s1 -> LTLE' f s2) /\ (LTLE' f s2 -> LTLE' f s1)).
Admitted.
(*
Proof.
  induction f.
  { intros.
    isc H.
    repeat (
        split;
        [intro H; isc H; constructor; first [rewrite H0 | rewrite <- H0]; auto|]). admit. }
  {
    intros. specialize (IHf _ _ H).
    destruct IHf.
    isc H.
    split.
    intros.


    { constructor; isc H.
      intros.
      destruct H.
      constructor. isc H0. rewrite <- H. auto. }
    { 
    split.
    {
  }
  fwd.
  Admitted.
(*
induction f.
  Focus 2.
  intros.
  split.
  intros. isc H0. constructor.
  isc H.
  { intros.
    isc H.
    rewrite H0 in *.
    split; [intros; constructor; rewrite H0 in *|].
    split. constructor.
    isc H. rewrite H0 in H4. assumption.
    intros.
    isc H.
    constructor. rewrite H0. assumption. }
  {
    intros.
split.
intros.

intros.

    isc H0. isc H.
    constructor. 
    rewrite H3 in H2. assumption. }
  { intros.
    isc H0. isc H.
    constructor.
    unfold lseq in *.
    isc H2.
    rewrite H0 in H2.
    rewrite H0.

  constructor; assumption. }
  { constructor.
  subst.
  red in H3.
  Print lseq.
  SearchAbout lseq.
  apply lseq_correct in H0.
  destruct H.

  inversion 1; subst.
*)
*)

(* Maybe I should get Greg's library, for the tactics.
   Or just grab some standard ones.
 *)

(* First we neeq equi-satisfiability? *)

Lemma LTLE_sanity :
  forall f st st', StreamEq st st' -> LTLE f st -> LTLE' f st' -> False.
Proof.
  induction f.

  Focus 5.
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