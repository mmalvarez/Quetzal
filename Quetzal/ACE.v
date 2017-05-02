(* ACE also known as All Coinductive Everything *)

CoInductive Cobool : Set :=
| ctrue
| cfalse.

(* far from clear if these are useful *)
CoInductive Cotype : Type -> Type :=
| CT : forall (T : Type), Cotype T.

CoInductive Coprop : Prop -> Type :=
| CP : forall (P : Prop), Coprop P.

CoInductive Coset : Set -> Type :=
| CS : forall (S : Set), Coset S.

CoInductive Coexist (A : Type) (F : A -> Type) : Type :=
| cintro : forall (a : A), F a -> Coexist A F.

Definition cp_inj : forall (P : Prop),
    Coprop P -> Cotype P :=
  fun P _ => CT P.

Definition CTt :=
  Coexist (forall (T : Type), Cotype T).

(* It would be ideal to use this as little as possible,
   since we would need to build all new rewriting infrastructure. *)
(* Also, this doesn't have the nice property that we'd like it to have
   (being able to easily compare coinductive objects) *)
CoInductive Coeq {A : Type} (x : A) : A -> Prop :=
  crefl : Coeq x x.

CoInductive Stream (A : Type) : Type :=
| scons : A -> Stream A -> Stream A.

Arguments scons {_} _ _.

Definition shd {A: Type} (s : Stream A) : A :=
  match s with
  | scons a _ => a
  end.

Definition stl {A : Type} (s : Stream A) : Stream A :=
  match s with
  | scons _ t => t
  end.

CoInductive Cofalse : Type :=.
CoInductive Counit : Type := Ctt.

(* TODO: should this use Coeq? *)
CoInductive Strcmp {T1 T2 : Type} (R : T1 -> T2 -> Prop) : Stream T1 -> Stream T2 -> Prop :=
| SEq : forall ah bh,
    R ah bh ->
    forall a b,
      Strcmp R a b ->
      Strcmp R (scons ah a) (scons bh b).

(* From CPDT, "Coinduction" *)
Section Strcmp_coind.
  Variable A B : Type.
  Variable R : A -> B -> Prop.
  Variable Rs : Stream A -> Stream B -> Prop.
  Hypothesis scons_case_shd : forall s1 s2, Rs s1 s2 -> R (shd s1) (shd s2).
  Hypothesis scons_case_stl : forall s1 s2, Rs s1 s2 -> Rs (stl s1) (stl s2).
  Theorem Strcmp_coind : forall s1 s2, Rs s1 s2 -> Strcmp R s1 s2.
  Proof.
    cofix.
    destruct s1; destruct s2; intros.
    generalize (scons_case_shd _ _ H). intro HR.
    simpl in HR.
    constructor.
    { apply HR. }
    apply Strcmp_coind.
    specialize (scons_case_stl _ _ H). simpl in scons_case_stl. assumption.
  Qed.
End Strcmp_coind.

Lemma Coeq_scons :
  forall (T : Type) (a b : Stream T),
    Strcmp Coeq a b ->
    Coeq a b -> forall (x : T),
        Coeq (scons x a) (scons x b).
Proof.
  intros. destruct H0. constructor.
Qed.

CoInductive Coand (T1 T2 : Type) : Type :=
| cconj : T1 -> T2 -> Coand T1 T2.

CoInductive Coor (T1 T2 : Type) : Type :=
| cintrol : T1 -> Coor T1 T2
| cintror : T2 -> Coor T1 T2.

(* still fails to hold even for coinductive equality *)
(* Perhaps this is valid, and comprises a notion of
   extensionality? *)
Lemma Coeq_strcmp :
  forall T s1 s2,
    Strcmp (@Coeq T) s1 s2 ->
    @Coeq (Stream T) s1 s2.
Proof.
  cofix.
  intros.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  eapply Coeq_scons.
  - assumption.
  - eapply Coeq_strcmp. assumption.
Abort. (* Qed. *)

Definition CoR {T : Type} (R : T -> T -> Prop) : T -> T -> Prop :=
  fun t1 t2 => (R t1 t2 -> Cofalse).

Lemma strcmp_false :
  forall T (R : T -> T -> Prop) s1 s2,
    Strcmp R s1 s2 ->
    Strcmp (CoR R) s1 s2 ->
    Cofalse.
Proof.
  cofix.
  intros.
  destruct s1. destruct s2.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  unfold CoR in H3. auto.
Qed.