Set Implicit Arguments.

Require Import Coq.Init.Nat.
Require Import BA.External.
Require Import BasicDefs.

(** * Sequences
    General operations and facts about sequences *)


Definition Seq (X:Type) := nat -> X.

Definition SeqLang (X:Type) := Language (Seq X).
Notation "x ^0$0" := (universal_language (X:=Seq x)) (at level 20).

(** ** Basic Operations on Sequences *)
Section SeqOperations.

  Context {X:Type}.

  (** Dropping the first n elements of a sequence *)
  Fixpoint drop n (w:Seq X) := match n with 
    | 0 => w
    | S n => drop n (fun n => w (S n))
  end.

  (** Prepending an element to a sequence *)
  Definition prepend a (w:Seq X) := fun n => match n with
    | 0 => a
    | S n => w n
   end.

  (** [prepend_path] prepends the first k+1 values of the sequence p on the sequence w,
      k+1 makes sence with respect to the definition of strings *)
  Fixpoint prepend_path  k (p:Seq X) (w:Seq X) :  Seq X := match k with
   | 0 => prepend (p 0) w
   | S k => prepend (p 0) (prepend_path k (drop 1 p)  w) 
   end.

  (** Cutting something from n exlusively to m inclusively out of a sequence *)
  Definition cut n m (w:Seq X) := prepend_path n w (drop m w).

  Lemma drop_correct n  (w:Seq X) : forall m, (drop n w) m = w (n + m).
  Proof.
    revert w.
    induction n; intros w m.
    - reflexivity.
    - apply IHn with (w:= (fun n => w ( S n))) (m:=m).
  Qed.
 
  Lemma prepend_first_correct a (w:Seq X):  ((prepend a w) 0) = a.
  Proof.
    reflexivity.
  Qed.

  Lemma prepend_rest_correct a (w:Seq X):  forall n, ((prepend a w) (S n)) = w n.
  Proof.
    reflexivity.
  Qed.

  Lemma prepend_rest_correct2 a (w: Seq X): forall n , n > 0 -> (prepend a w) n = w (pred n).
  Proof.
    intros n L.
    destruct n; oauto.
  Qed.

  Lemma prepend_path_begin_correct k p w n: n <= k -> prepend_path k p w n = p n.
  Proof.
   revert p w n.
   induction k; intros p w n L.
   - simpl. rewrite_eq (n = 0).
     apply prepend_first_correct.
   - simpl.
     destruct n.
     + apply prepend_first_correct.
     + rewrite prepend_rest_correct2 by omega.
       change (prepend_path k (drop 1 p) w n = (drop 1 p) n).
       apply IHk.
       omega.
  Qed.

  Lemma prepend_path_first k p w: (prepend_path k  p w) 0 = p 0.
  Proof.
    apply prepend_path_begin_correct. omega.
  Qed.

  Lemma prepend_path_rest_correct k p w n: (prepend_path k p w) (S k + n) = w n.
  Proof.
    revert p w n.
    induction k; intros p w n.
    - now reflexivity.
    - simpl. rewrite_eq (S (k + n) = S k +n).
      apply IHk.
  Qed.

  Lemma prepend_path_rest_correct2 k p w m n: (m = S k + n) -> (prepend_path k p w) m = w n.
  Proof.
    intros H.
    rewrite H.
    apply prepend_path_rest_correct.
  Qed.

  Lemma cut_front_correct n m w : forall k, k <= n -> (cut n m w) k = w k.
  Proof.
    intros k L.
    unfold cut.
    now rewrite prepend_path_begin_correct.
  Qed.

  Lemma cut_rest_correct n m w: forall k, (cut n m w) (S n + k) = w (m + k).
  Proof.
    intros k.
    unfold cut.
    rewrite prepend_path_rest_correct.
    now rewrite drop_correct.
  Qed.

  Lemma revert_prepend_path k (w w': Seq X): forall n, drop (S k) (prepend_path k w' w) n = w n.
  Proof.
    intros n.
    rewrite drop_correct.
    now rewrite prepend_path_rest_correct.
  Qed.

  Lemma revert_drop_path k (w : Seq X) : forall n, prepend_path k w (drop (S k) w) n = w n.
  Proof.
    intros n.
    decide (n <= k).
    - rewrite prepend_path_begin_correct; auto.
    - remember (n - S k ) as z.
      rewrite_eq (n = S k + z).
      rewrite prepend_path_rest_correct.
      now rewrite drop_correct.
   Qed.

   (** Mapping function on sequences *)
   Definition seq_map (A1 A2 : Type) (f: A1 -> A2) (w : Seq A1) : (Seq A2) := fun n => f (w n).

End SeqOperations.

(** ** An element occuring infinitely often in a Sequence *)
Section Infinite.
  Context {X:Type}.

  Definition infinite (x:X) (w:Seq X) := forall n, exists m, m>=n /\ (w m) = x.

  Lemma finite_prefix_preserves_infinite k p w s: infinite s w -> infinite s (prepend_path k p w).
  Proof.
    intros I n.
    destruct (I n) as [m [P Q]].
    exists (S k + m).
    split.
    - omega.
    - now rewrite prepend_path_rest_correct.
  Qed.

  Lemma drop_preserves_finite s w n: infinite s w -> infinite s (drop n w).
  Proof.
    intros I k.
    destruct (I (k+n)) as [m [P Q]].
    exists (m-n). split.
    - omega.
    - rewrite drop_correct.
      rewrite <-Q. f_equal. omega.
  Qed.
End Infinite.

(** ** Pointwise equiality of sequences *)
Definition seq_equal (X:Type)(w1 w2 : Seq X) := forall n, w1 n = w2 n.
Notation "w1 === w2" := (seq_equal w1 w2) (at level 70).
Hint Unfold seq_equal.

(** ** Decidability of bounded quantifiers on Sequences *)
Instance seq_dec_exists_bounded (X: Type)(P: X -> Prop) (decP: forall n, dec (P n)) (w : Seq X) n: dec( exists k, k <= n /\ P (w k)).
Proof.
  induction n.
  - decide (P (w 0)) as [D|D].
    + left. firstorder.
    + right. intros [k [L Q]]. now rewrite_eq (k = 0) in Q.
  - decide (P (w (S n))) as [D|D].
    + left. exists (S n); auto.
    + destruct (IHn) as [D'|D'].
      * left. firstorder.
      * right. intros [k [L Q]].
        decide (k <= n).
        -- apply D'. exists k; auto.
        -- apply D. now rewrite_eq (S n = k).
Defined. 

Instance dec_bounded_nat_forall (P: nat -> Prop) (decP: forall n, dec (P n)) m : dec (forall n, n <= m -> P n).
Proof.
  destruct (seq_dec_exists_bounded  (P:= fun n => ~ P n) _ (fun (n:nat) => n) m).
  - right. firstorder.
  - left. firstorder.
Defined. 

Instance dec_strict_bounded_nat_forall (P: nat -> Prop) (decP: forall n, dec (P n)) m : dec (forall n, n < m -> P n).
Proof.
  destruct m.
    - left. intros n L. exfalso. omega.
    - destruct (dec_bounded_nat_forall decP m).
    + left. firstorder.
    + right. firstorder.
Defined. 

Lemma seq_prop_dec_exists_bounded (X:Type) (p: X ->Prop) (L: Seq X) (l: nat): (forall x, p x \/ ~ p x)  -> (exists i, i <= l /\ p (L i)) \/ (forall i, i <= l -> ~ p (L i)).
Proof.
  intros pD.
  induction l.
  - simpl. destruct (pD (L 0)) as [H|H].
    + left. firstorder.
    + right. intros i O. now rewrite_eq (i = 0).  
  - destruct IHl as [[i [O P]] | IHl].
    + simpl in O,P. left. firstorder.
    + destruct (pD (L (S l))) as [H|H].
      * left. firstorder.
      * right. intros i O.
        decide (i = S l) as [D|D].
        -- now subst i.
        -- apply (IHl i). omega.
Qed.


Delimit Scope string_scope with string. 

(** * Strings *)
(** A String is a nonempty prefix on a sequence: [lastindex] is the last index in [seq]
    which belongs to the string
    Deriving strings from sequences makes operations on both uinform on easier *)
Structure String (X:Type) := mkstring {seq :> Seq X; lastindex : nat}.

Notation "| v |" := (lastindex v) : string_scope.
Notation "v [ k ]" := ((seq v) k) (at level 10) : string_scope.

Open Scope string_scope.

(** ** Equality Relation on Strings
    Because strings consist of sequences, there is no usable equality on them.
    Define the pointwise equality relation. *)
Section StringsEq.
  Context {X: Type}.

  Definition strings_equal (w w': String X):= |w| = |w'| /\ (forall n, n <= |w| -> w [n] = w' [n]).

  Lemma string_equal_reflexive: reflexive (String X) strings_equal.
  Proof.
    intros w. split; auto.
  Qed.

  Lemma string_equal_symmetric : symmetric (String X) strings_equal.
  Proof.
    intros w w' [EL EW]. split.
    - omega.
    - intros n L. symmetry. apply (EW n). omega.
  Qed.  
End StringsEq.


(** ** Simple Operations on Strings *)
Section StringOperations.
  Context {X:Type}.

  Definition concat_strings (v w : String X ) : String X := mkstring (prepend_path (|v|) v w) ((|v|) + S(|w|)).

  Definition drop_string_begin n (w: String X) := mkstring (drop n w) ((|w|) - n).
  Definition drop_string_end n (w: String X) := mkstring w ((|w|) - n).

  (** Extracts the string from [w] starting at index [n] (inclusively) until index [m] (exclusively) *)
  Definition extract n m (w : Seq X) : String X:= mkstring(drop n w) (m - S n).

  Lemma extract_correct n m w: forall k, (extract n m w) [k] = w (n + k).
  Proof.
    intros k.
    simpl.
    apply drop_correct.
  Qed.

End StringOperations.

Notation "v ++ w" := (concat_strings v w) : string_scope.
Notation "v +++ w" := (prepend_path (|v|) v w) (at level 60) : string_scope .
Notation "v == w" := (strings_equal v w) (at level 65): string_scope.

(** ** Equality of results of some string operations *)
Lemma revert_concat_first (X:Type)(v w:String X): v == drop_string_end (S(|w|)) (v ++ w).
Proof.
  unfold drop_string_end. simpl. split.
  - simpl. omega.
  - intros n L. simpl. now rewrite prepend_path_begin_correct.
Qed.

Lemma revert_concat_second (X:Type)(v w:String X): w == drop_string_begin (S(|v|)) (v ++ w).
Proof.
  unfold drop_string_begin. split.
  - simpl. omega.
  - intros n L. simpl. rewrite drop_correct.
    rewrite_eq (S((|v|) + n) = S (|v|) + n). now rewrite prepend_path_rest_correct.
Qed. 

Lemma concat_extract (X:Type) (w : Seq X) i1 i2 i3: i1 < i2 -> i2 < i3 -> ((extract i1 i2 w) ++ (extract i2 i3 w)) == (extract i1 i3 w).
Proof.
  intros L1 L2.
  split.
  - simpl. omega.
  - intros n L.
    simpl. decide (n <= (i2 - S i1)) as [D|D].
    + now rewrite prepend_path_begin_correct by omega.
    + remember (n - S(i2 -  S i1)) as z.
      rewrite_eq (n = S(i2 - S i1) + z).
      rewrite prepend_path_rest_correct.
      repeat rewrite drop_correct. f_equal. omega.
Qed.

Lemma extract_from_drop (X:Type) (w:Seq X) n m k: (extract n m (drop k w)) == (extract (n + k) (m + k) w).
Proof.
  repeat split; simpl; oauto.
  intros i B. simpl. repeat rewrite drop_correct.
  f_equal. omega.
Qed.

 
(** ** Languages of Strings *)
Definition StringLang (A: Type) := Language (String A).

(** Extensionality on strings: a string language is extensional if it does only care about the values of the valid indicies of w*)
Definition StringLang_Extensional (A:Type) (l: StringLang A):= forall (w w' : String A ), l w ->  w == w' -> l w'.

