Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Prop_Bi_Int_calcs.
Require Import Prop_Bi_Int_Kripke_sem.


Lemma Ax_valid : forall A, BIAxioms A ->
  (forall W R R_props val pers w, wforces W R R_props val pers w A).
Proof.
intros A Ax. inversion Ax ; destruct H ; subst ; destruct R_props ;
unfold R_refl in r ; unfold R_trans in r0 ; simpl ; intros ; auto.
- destruct H ; destruct H ; subst ; simpl ; intros ; auto. apply H2 ; auto. apply H0 ; auto. apply r0 with (v:=v0) ; auto.
- destruct H ; subst ; simpl ; intros ; auto.
- destruct H ; subst ; simpl ; intros ; auto ;  destruct H0 ; auto.
- destruct H ; destruct H ; subst ; simpl ; intros ; auto. destruct H4 ; auto. apply H0 ; auto.
  apply r0 with (v:=v0) ; auto.
- destruct H ; subst ; simpl ; intros ; auto. destruct H0. auto.
- destruct H ; subst ; simpl ; intros ; auto. destruct H0. auto.
- destruct H ; destruct H ; subst ; simpl ; intros ; auto. split.
  apply H0 ; auto. apply r0 with (v:=v0) ; auto. apply H2 ; auto.
- destruct H ; destruct H ; subst ; simpl ; intros ; auto.
  apply H0 with (v:=v0) (v0:=v0) ; auto. destruct H2. assumption.
  destruct H2. assumption.
- destruct H ; destruct H ; subst ; simpl ; intros ; auto.
  apply H0 ; auto. apply r0 with (v:=v0) ; auto. split. apply Persistence with (w:=v0) ; auto.
  auto.
- destruct H ; subst ; simpl ; intros ; auto.
  apply H2 with (v:=v1) ; auto. apply H0 ; auto. apply r0 with (v:=v1) ; auto. apply r0 with (v:=v0) ; auto.
- destruct H ; subst ; simpl ; intros ; auto.
  pose (@wforces_dec x0 W R (r, r0) val pers v). destruct o. auto.
  right. exists v. repeat split. apply r. assumption. assumption.
- destruct H ; subst ; simpl ; intros ; auto.
  destruct H0. destruct H0. destruct H1. exists x1 ; auto.
- destruct H ; destruct H ; subst ; simpl ; intros ; auto.
  destruct H0. destruct H0. destruct H1. destruct H1. destruct H1. destruct H3.
  exists x3. repeat split ; auto. apply r0 with (v:=x2) ; auto. intro.
  destruct H5. apply H4. auto. apply H2. apply Persistence with (w:=x3). auto.
  assumption.
- destruct H ; subst ; simpl ; intros ; auto.
  pose (@H0 v0 H1). pose (@wforces_dec x0 W R (r, r0) val pers v0). destruct o ; auto.
  exfalso. apply f. exists v0 ; repeat split ; auto.
- inversion H0.
Qed.

Theorem wSoundness0 : forall s, (wBIC_rules s) ->
        (loc_conseq (fst s) (Singleton _ (snd s))).
Proof.
intros s D. induction D.
(* Id *)
- inversion H. subst. simpl. intro. intros. exists A. split. apply In_singleton.
  apply H1. assumption.
(* Ax *)
- inversion H. subst. simpl. intro. intros. exists A. split. apply In_singleton.
  apply Ax_valid. assumption.
(* MP *)
- inversion H1. subst. simpl. assert (J1: loc_conseq ?? (Singleton (BPropF V) (A ??? B))).
  apply H0 with (prem:=(??, A ??? B)). apply in_eq. assert (J2: loc_conseq ?? (Singleton (BPropF V) (A))).
  apply H0 with (prem:=(??, A)). apply in_cons. apply in_eq.
  intro. intros.
  exists B. split. apply In_singleton. unfold loc_conseq in J1.
  pose (J1 W R R_props val pers w H2). destruct e. destruct H3. inversion H3. subst.
  pose (J2 W R R_props val pers w H2). destruct e. destruct H5. inversion H5.
  subst. apply H4. destruct R_props. apply r. assumption.
(* DNw *)
- inversion H1. subst. simpl. assert (J1: loc_conseq (Empty_set (BPropF V)) (Singleton (BPropF V) (A))).
  apply H0 with (prem:=(Empty_set (BPropF V), A)) ; apply in_eq.
  intro. intros. exists (Neg (wNeg A)). split. apply In_singleton.
  simpl in J1. simpl. intros. destruct H4. destruct H4. apply H5.
  assert (J2: (forall A : BPropF V, In _ (Empty_set _) A -> wforces W R R_props val  pers x A)).
  intros. inversion H6.
  pose (J1 W R R_props val pers x J2). destruct e. destruct H6. inversion H6. subst.
  assumption.
Qed.

Lemma list_disj_witn : forall W R R_props val  pers w l,
    (wforces W R R_props val  pers w (list_disj l)) ->
    (exists A : BPropF V, (List.In A l) /\ wforces W R R_props val  pers w A).
Proof.
induction l.
- simpl. intros. inversion H.
- simpl. intros. destruct H.
  * exists a. split. apply in_eq. assumption.
  * apply IHl in H. destruct H. destruct H. exists x. split ; try assumption. apply in_cons ; auto.
Qed.

Theorem wSoundness : forall (?? ?? : @Ensemble (BPropF V)), wpair_derrec (??, ??) -> (loc_conseq ?? ??).
Proof.
intros ?? ?? wpair. destruct wpair. destruct H. destruct H0. simpl in H0.
simpl in H1. apply wSoundness0 in H1. simpl in H1. intro. intros. unfold loc_conseq in H1.
pose (H1 W R R_props val pers w H2). destruct e. destruct H3. inversion H3. subst.
induction x.
- simpl in H1. exfalso. simpl in H3. simpl in H4. inversion H4.
- simpl in IHx. simpl in H3. simpl in H4. destruct H4.
  * exists a. split. apply H0. apply in_eq. assumption.
  * apply list_disj_witn in H4. destruct H4. destruct H4. exists x0. split.
    apply H0. apply in_cons. 2: assumption. assumption.
Qed.

Theorem sSoundness0 : forall s, (sBIC_rules s) ->
        (glob_conseq (fst s) (Singleton _ (snd s))).
Proof.
intros s D. induction D.
(* Ids *)
- inversion H. subst. simpl. intro. intros. exists A. split. apply In_singleton.
  apply H1. assumption.
(* Axs *)
- inversion H. subst. simpl. intro. intros. exists A. split. apply In_singleton.
  apply Ax_valid. assumption.
(* MPs *)
- inversion H1. subst. simpl. assert (J1: glob_conseq ?? (Singleton (BPropF V) (A ??? B))).
  apply H0 with (prem:=(??, A ??? B)). apply in_eq. assert (J2: glob_conseq ?? (Singleton (BPropF V) (A))).
  apply H0 with (prem:=(??, A)). apply in_cons. apply in_eq.
  intro. intros.
  exists B. split. apply In_singleton. unfold glob_conseq in J1.
  pose (J1 W R R_props val pers H2 w). destruct e. destruct H3. inversion H3. subst.
  pose (J2 W R R_props val pers H2 w). destruct e. destruct H5. inversion H5.
  subst. apply H4. destruct R_props. apply r. assumption.
(* DNs *)
- inversion H1. subst. simpl. assert (J1: glob_conseq (??) (Singleton (BPropF V) (A))).
  apply H0 with (prem:=(??, A)) ; apply in_eq.
  intro. intros. exists (Neg (wNeg A)). split. apply In_singleton.
  simpl in J1. simpl. intros. destruct H4. destruct H4. apply H5.
  pose (J1 W R R_props val pers H2 x). destruct e. destruct H6. inversion H6. subst.
  assumption.
Qed.

Theorem sSoundness : forall (?? ?? : @Ensemble (BPropF V)), spair_derrec (??, ??) -> (glob_conseq ?? ??).
Proof.
intros ?? ?? gpair. destruct gpair. repeat destruct p. destruct H. destruct H0. simpl in H0.
simpl in H1. apply sSoundness0 in H1. simpl in H1. intro. intros.
induction x.
- simpl in H1. exfalso. pose (H1 W R R_props val pers H2 w). destruct e. destruct H3.
  inversion H3. subst. auto.
- pose (H1 W R R_props val pers H2 w). destruct e. destruct H3. inversion H3. subst.
  simpl in H1. simpl in H4. destruct H4.
  * exists a. split. apply H0. apply in_eq. assumption.
  * apply list_disj_witn in H4. destruct H4. destruct H4. exists x0. split.
    apply H0. apply in_cons. assumption. assumption.
Qed.
