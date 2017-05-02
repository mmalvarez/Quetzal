(* Set Implicit Arguments. *)
Require Import BA.External.
Require Import Seqs.
Require Import BasicDefs.
Require Import BA.FinTypes.

(** * Some Utilities *)

(** ** Finite type {n|n<=k} 
    This is not the most beautiest code since it is obvious that this is a finite type *)
Section FirstKFinType.

  (** Construct the list of all numbers <= k *)
  
  Definition le_k k := fun n => n <= k.
  Instance dec_le_k k n : dec ( le_k k n). Proof. auto. Defined.

  Definition Le_K k := {n | (pure (le_k k)) n}.

  Fixpoint all_le_k k : list nat := match k with
    | 0 => [0]
    | S k => (S k) :: (all_le_k k) end.

  Instance dec_pure_le_k k n : dec (pure (le_k k) n).
  Proof.
   decide (le_k k n) as[D|D].
   - left. now apply pure_equiv. 
   - right. intros L. apply D. now apply pure_equiv in L.
  Defined.

  Hint Resolve dec_pure_le_k.

  Lemma pure_le_k_if k n : n <= k -> pure (le_k k) n.
  Proof.
    intros L.
    now rewrite <-pure_equiv.
  Qed.

  (** Construct the list of all numbers <= k including the proof *)

  Definition all_Le_K k n := (fix f (L: list nat) := match L with
      | [] => []
      | n::L => match  (decision (pure (le_k k) n)) with
                 | left D => (exist (pure (le_k k)) n D) :: f L
                 | right D => f L
                   end end) (all_le_k n).

  (** Proof completeness and dupfreeness to assert that this list contains all
      elements of this type exactely once *)

  Lemma in_all_le_k_iff k n: n<= k <-> n el all_le_k k.
  Proof.
   induction k.
   - split.
     + intros L. simpl. left. omega.
     + intros [E|E]. omega. contradiction E.
   - split.
     + intros L. decide (n = S k).
       * rewrite e. simpl. now left.
       * simpl. right. apply IHk. omega.
     + intros E. decide (n = S k).
       * omega.
       * enough (n <= k). omega.
         apply IHk. destruct E as [E|E].
         -- apply IHk. omega.
         -- assumption.
  Qed. 

  Lemma dup_free_all_le_k k: dupfree (all_le_k k).
  Proof.
    induction k.
    - simpl. constructor.
      + auto.
      + constructor.
    - simpl. constructor.
      + intros E. apply in_all_le_k_iff in E. omega.
      + assumption.
  Qed.

  Lemma in_all_Le_K_if k (x : Le_K k): x el all_Le_K k k.
  Proof.
    unfold all_Le_K.
    destruct x as [n L].
    pose (L' := L).
    rewrite <-pure_equiv in L'.
    pose (Q:= in_all_le_k_iff k n).
    destruct Q. specialize (H L').
    induction (all_le_k k).
    - contradiction H.
    - destruct H.
      + rewrite H.
        decide (pure (le_k k) n).
        *  simpl. left.
           f_equal. apply pure_eq.
        *  exfalso. apply n0. now apply pure_le_k_if.
      + decide (pure (le_k k) a).
        *  simpl. right. apply IHl; auto.
        *  apply IHl; auto.
  Qed.

  Lemma in_all_Le_K_if2 k x : x el all_Le_K k k -> match x with exist _ x L => x <= k end.
  Proof.
    destruct x. intros _.  change ((le_k k) x). rewrite pure_equiv. apply p.
  Qed.

  Lemma in_all_Le_K_ifLess k k' x :k <= k'->  x el all_Le_K k' k -> match x with exist _ x _ => x <= k end.
  Proof.
    unfold all_Le_K.
    intros L.
    induction k.
    - simpl. destruct (pure_equiv 0). destruct x. intros [E|E].
      + enough (x = 0). omega.
        congruence.
      + contradiction E.
    - simpl.    decide (pure (le_k k') (S k)) as [D|D].
      + simpl. intros [E|E].
        * destruct x. enough (x = S k). omega. congruence.
        * destruct x. enough (x <= k). omega.
          apply IHk; auto. omega.
      + exfalso. apply D. apply pure_le_k_if. omega.
  Qed.

  Lemma dup_free_all_Le_K k n : n <= k -> dupfree (all_Le_K k n).
  Proof.
    unfold all_Le_K. revert k.
    induction n; intros k L.
    - simpl. constructor.
      + auto.
      + constructor.
    - simpl. decide (pure (le_k k) (S n)).
      + constructor.
        * intros E. apply in_all_Le_K_ifLess in E. omega. omega.
        * apply IHn. omega.
      + apply IHn. omega.
  Qed.

  Section DeclareFinType.
    Variable (k:nat).
     
    Instance LE_K_eq_dec  : eq_dec (Le_K k).
    Proof.
      intros [n1 p1] [n2 p2].
      decide (n1 = n2).
      - left. destruct e. f_equal. now apply pure_eq. 
      - right. intros L. apply n.
        congruence.
    Defined.
    Canonical Structure EqLe_K := EqType (Le_K k).

    Lemma Le_K_enum_ok  (x : EqLe_K ) : count (X:= EqLe_K ) (all_Le_K k k) x =1.
    Proof.
      apply dupfreeCount.
      - apply dup_free_all_Le_K. omega.
      - apply in_all_Le_K_if.
    Qed.

    Instance finTypeC_Le_K : finTypeC EqLe_K.
    Proof.
      econstructor. apply Le_K_enum_ok.
    Defined.
    Canonical Structure finType_Le_K : finType := FinType EqLe_K.
  End DeclareFinType.

  (** All numbers [n <= k] can be converted to this type *)

  Lemma create_Le_K n k (L: n <= k) : Le_K k.
  Proof.
   exists n.
   apply pure_equiv. unfold le_k. exact L.
  Defined.

  (** *** Cardinality is [S k] *)

  Lemma all_Le_K_length_all_le_k n k : n<= k -> length (all_Le_K k n) = S n.
  Proof.
    unfold all_Le_K. revert k.
    induction n; intros k L.
    - simpl. reflexivity.
    - simpl. destruct decision as [D|D].
      + simpl. f_equal. apply IHn. omega.
      + exfalso. apply D. now rewrite <-pure_equiv.
  Qed.   

  Lemma card_finTypeC_Le_K k : length(enum (finTypeC := finTypeC_Le_K k )) = S k.
  Proof.
    unfold finType_Le_K. simpl.
    now apply all_Le_K_length_all_le_k.
  Qed.

  Lemma card_finType_Le_K k : Cardinality( finType_Le_K k ) = S k.
  Proof.
    unfold Cardinality. apply card_finTypeC_Le_K.
  Qed.

  (** *** Decisions for this Type *)

  Lemma bounded_type_exist k (P:  (Le_K k) -> Prop) (decP: forall  L, dec (P  L)): dec( exists L, P  L).
  Proof.
   - auto using finType_exists_dec.
  Qed.

  Lemma bounded_exist k (P:nat -> Prop) (decP: forall n, dec (P n)): dec(exists n, n <= k /\ P (n)).
  Proof.
    pose (P' := fun (n:Le_K k) => match n with exist _ n _ => P n end).
    enough (dec (exists (n:Le_K k), P' n)) as H.
    - destruct H as [H|H].
      + left. destruct H as [[n p] Pn].
        exists n. split.
        * change (le_k k n). rewrite pure_equiv. exact p.
        * now simpl in Pn.
      + right. intros [n [L Pn]].
        apply H.  change (le_k k n) in L. rewrite pure_equiv in L. 
        exists (exist (pure (le_k k)) n L).
        now simpl.
    - apply bounded_type_exist. intros L. unfold P'. now destruct L.
  Qed.

  Lemma strict_bounded_exist k (P:nat -> Prop) (decP: forall n, dec (P n)): dec(exists n, n < k /\ P (n)).
  Proof.
    destruct k.
    - right. intros [n [L _]]. omega.
    - destruct  (bounded_exist k  decP) as [D|D].
      + left. destruct D as [ n [ L Q]]. exists n. split; oauto.
      + right. intros [n [L Q]]. apply D. exists n. split; oauto.
  Qed. 

End FirstKFinType.

Hint Resolve bounded_exist.
Hint Resolve strict_bounded_exist.

Instance dec_pure_le_k_public x y : dec (pure (le_k x) y).
Proof. apply dec_pure_le_k.  Defined.
Hint Resolve dec_pure_le_k_public. (* The other does not work for some reasons even it is registered*)


(** ** Interpretation of {n|n<=k} as Prefix of Sequences *)
Section ConvertFinTypeToSeq.

  Context {m : nat}.
  Context {X : finType}.

  Lemma dummy : (finType_Le_K m).
  Proof.
    exists 0. apply pure_equiv. unfold le_k. omega.
  Qed.

  Definition to_seq (b:X^(finType_Le_K m)) := fun (n:nat) =>  match  (decision (pure (le_k m) n) ) with
                                   | left D =>  applyVect b (exist (pure (le_k m )) n D)
                                   | right D => applyVect b dummy
                                       end.
  Definition to_bounded(r:Seq X): X^(finType_Le_K m) := vectorise (fun (n:(finType_Le_K m)) => match n with exist _ n _ => r n end).

  Lemma to_bounded_unchanged (r:Seq X) n (L: n <= m ): applyVect (to_bounded r) (create_Le_K L)  = r n.
  Proof.
    unfold to_bounded.
    rewrite apply_vectorise_inverse.
    now simpl.
  Qed. 

  Lemma to_seq_unchanged (r:X^(finType_Le_K m)) n (L: n <= m ): to_seq r n = applyVect r (create_Le_K L).
  Proof.
    unfold to_seq.
    destruct (decision (pure (le_k m) n)) as [D|D].
    - f_equal. unfold create_Le_K.
      f_equal. apply pure_eq.
    - exfalso. apply D. now apply pure_equiv.
  Qed. 
  

   Lemma bounded_unchanged (r:Seq X) n : n <=m-> to_seq  (to_bounded r) n = r n.
  Proof.
   intros L.
   rewrite (to_seq_unchanged (to_bounded r) L).
   apply to_bounded_unchanged.
  Qed. 

End ConvertFinTypeToSeq.

(** ** Duplicates in a String of a Finite Type *)

Lemma can_find_duplicate (X: finType) k (r: Seq X) : (Sigma n1 n2, n1 < n2 <= k /\ r n1 = r n2) + {k <= Cardinality X }.
Proof.
  decide (k <= Cardinality X).
  - now right.
  - left.
    assert (k > Cardinality X) as H by omega.
    pose (f := fun (k : finType_Le_K k) => match k with exist _ k _ => r k end ).
    pose (P := fun (n1 n2 : finType_Le_K k) => match n1, n2 with
             (exist _ n1 _), (exist _ n2 _) => n1 < n2 <= k /\ r n1 = r n2 end).
    assert (forall n1 n2, dec(P n1 n2)) as decP. { intros [n1 ?] [n2 ?]. simpl. auto. }
    assert (forall n1, dec (exists (n2 : finType_Le_K k), P n1 n2)) as decP'. {  auto using finType_exists_dec. }
    assert (dec (exists (n1 n2 : finType_Le_K k), P n1 n2)) as D. {  auto using finType_exists_dec. }
    destruct D as[ D|D].
    +  destruct (finType_cc decP') as [n1 p1]. { destruct D as [n1 p]. now exists n1. }
       destruct (finType_cc (decP n1)) as [n2 p2]. { destruct p1 as [n2 p]. now exists n2. }
       destruct n1 as [n1 ?]; destruct n2 as [n2 ?].
       exists n1; exists n2.
       now simpl in p2.
    +  exfalso.
       assert (injective f) as I. {
         intros x y E.
         decide (x = y).
         - assumption.
         - exfalso. apply D.
           destruct x as [x' px] eqn:EX; destruct y as [y' py] eqn:EY.
           decide (x' < y').
           + exists x; exists y. unfold P.
             rewrite EX,EY. repeat split.
             * assumption.
             * change ((le_k k) y'). rewrite pure_equiv. apply py.
             * now unfold f in E.
           + assert (y' <> x'). { intros Eq. apply n0. destruct Eq. f_equal. apply pure_eq. }
             assert (y' < x') by omega.
             exists y; exists x. unfold P.
             rewrite EX,EY. repeat split.
             * assumption.
             * change ((le_k k) x'). rewrite pure_equiv. apply px.
             * now unfold f in E.
       }
       pose (J := pidgeonHole_inj I).
       rewrite card_finType_Le_K in J.
       omega.
Qed.

(** ** Maximum of finitely many Numbers *)

Fixpoint max_of_nat_string w l:= match l with
  | 0 => w 0
  | S l => max (w (S l)) (max_of_nat_string w l) end.

Lemma max_of_nat_string_correct v l: forall n , n<=l -> (v n) <= max_of_nat_string v l.
Proof.
  induction l; intros n L.
  - now rewrite_eq (n = 0).
  - simpl. decide (n = S l) as[D|D].
    + apply max_le_left. rewrite D. omega.
    + apply max_le_right. apply IHl. omega.
Qed.

(** ** Two list are equal if nth_error is equal for all n *)
Lemma list_eq (X: Type) (l1 l2: list X) : (forall n, nth_error l1 n= nth_error l2 n) -> l1 = l2.
Proof.
  revert l2.
  induction l1; intros l2 EE.
  - specialize (EE 0). simpl in EE. now destruct l2.
  - destruct l2.
    + now specialize (EE 0).
    + f_equal.
      * specialize (EE 0). simpl in EE. congruence.
      * apply IHl1.
        intros n. specialize (EE (S n)). now simpl in EE.
Qed.

(** ** Constructive Choice for [nat]
    Taken from ICL *)

Inductive safe (p : nat -> Prop) (n : nat) : Prop :=
| safeB : p n -> safe p n
| safeS : safe p (S n) -> safe p n.

Lemma safe_dclosed k n p : k <= n -> safe p n -> safe p k.
Proof.
  intros A B. induction A as [|n A].
  - exact B.
  - apply IHA. right. exact B.
Qed.

Section First.
  Variable p : nat -> Prop.
  Variable p_dec : forall n, dec (p n).

  Fixpoint first (n : nat) (A : safe p n) : {k | p k} :=
    match p_dec n with
    | left B => exist p n B
    | right B => first match A with
    | safeB C => match B C with end
    | safeS A' => A'
    end
  end.

  Lemma cc_nat : (exists x, p x) -> {x | p x}.
  Proof.
    intros A. apply first with (n:=0).
    destruct A as [n A].
    apply safe_dclosed with (n:=n). omega. left. exact A.
  Qed.

End First.