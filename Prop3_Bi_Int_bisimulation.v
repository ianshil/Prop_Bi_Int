Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Prop3_Bi_Int_calcs.
Require Import Prop3_Bi_Int_Kripke_sem.


(* Define the notion of bisimulation. *)

Definition bisimulation
  W0 R0 (R0_props : R_refl R0 * R_trans R0) (val0 : W0 -> V -> Prop) (pers0 : val_persist_R W0 val0 R0)
  W1 R1 (R1_props : R_refl R1 * R_trans R1) (val1 : W1 -> V -> Prop) (pers1 : val_persist_R W1 val1 R1)
  (B : W0 -> W1 -> Prop) : Prop := forall (w0 : W0) (w1 : W1), (B w0 w1) ->
 (* B1 *) ((forall (p : V), (val0 w0 p) <-> (val1 w1 p)) /\
 (* B2 *) (forall v1, (R1 w1 v1) -> (exists (v0 : W0), (R0 w0 v0) /\ (B v0 v1))) /\
 (* B3 *) (forall v0, (R0 w0 v0) -> (exists (v1 : W1), (R1 w1 v1) /\ (B v0 v1))) /\
 (* B4 *) (forall v1, (R1 v1 w1) -> (exists (v0 : W0), (R0 v0 w0) /\ (B v0 v1))) /\
 (* B5 *) (forall v0, (R0 v0 w0) -> (exists (v1 : W1), (R1 v1 w1) /\ (B v0 v1)))).

(* Show that bisimulation implies bi-intuitionistic equivalence. *)

Lemma bisimulation_imp_bi_int_equiv : forall
 W0 R0 (R0_props : R_refl R0 * R_trans R0) (val0 : W0 -> V -> Prop) (pers0 : val_persist_R W0 val0 R0)
 W1 R1 (R1_props : R_refl R1 * R_trans R1) (val1 : W1 -> V -> Prop) (pers1 : val_persist_R W1 val1 R1)
 (B : W0 -> W1 -> Prop),
  (bisimulation W0 R0 R0_props val0 pers0 W1 R1 R1_props val1 pers1 B) ->
  (forall A w0 w1, (B w0 w1) ->
    ((wforces W0 R0 R0_props val0 pers0 w0 A) <-> (wforces W1 R1 R1_props val1 pers1 w1 A))).
Proof.
intros W0 R0 R0_props val0 pers0 W1 R1 R1_props val1 pers1 B H.
induction A ; split ; intro.
  * simpl. simpl in H1. unfold bisimulation in H. pose (H w0 w1 H0).
    destruct a. apply H2. auto.
  * simpl. simpl in H1. unfold bisimulation in H. pose (H w0 w1 H0).
    destruct a. apply H2. auto.
  * simpl. inversion H1.
  * simpl. inversion H1.
  * simpl in H1. apply I.
  * apply I.
  * simpl in H1. destruct H1. simpl. split. pose (IHA1 w0 w1 H0). apply i. auto.
    pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. destruct H1. simpl. split. pose (IHA1 w0 w1 H0). apply i. auto.
    pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. simpl. destruct H1. left. pose (IHA1 w0 w1 H0). apply i. auto.
    right. pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl in H1. simpl. destruct H1. left. pose (IHA1 w0 w1 H0). apply i. auto.
    right. pose (IHA2 w0 w1 H0). apply i. auto.
  * simpl. simpl in H1. intros. unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H4. destruct H5. clear H5.
    pose (H4 _ H2). destruct e. destruct H5.
    pose (IHA1 x v H6). apply i in H3. apply H1 in H3. 2: auto.
    pose (IHA2 x v H6). apply i0. auto.
  * simpl. simpl in H1. intros. unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H4. destruct H5. clear H4.
    destruct H5. clear H5.
    pose (H4 _ H2). destruct e. destruct H5.
    pose (IHA1 v x H6). apply i in H3. apply H1 in H3. 2: auto.
    pose (IHA2 v x H6). apply i0. auto.
  * simpl. simpl in H1. destruct H1. destruct H1. destruct H2.
    unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H4. destruct H5. clear H4.
    destruct H5. clear H4. destruct H5. clear H4.
    pose (H5 _ H1). destruct e. destruct H4. exists x0.
    pose (IHA1 x x0 H6). apply i in H2.
    pose (IHA2 x x0 H6). repeat split ; auto. intro.
    apply i0 in H7. apply H3. auto.
  * simpl. simpl in H1. destruct H1. destruct H1. destruct H2.
    unfold bisimulation in H.
    pose (H w0 w1 H0). destruct a. clear H4. destruct H5. clear H4.
    destruct H5. clear H4. destruct H5. clear H5.
    pose (H4 _ H1). destruct e. destruct H5. exists x0.
    pose (IHA1 x0 x H6). apply i in H2.
    pose (IHA2 x0 x H6). repeat split ; auto. intro.
    apply i0 in H7. apply H3. auto.
Qed.








