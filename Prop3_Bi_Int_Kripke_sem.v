Require Import Classical.
(* Used in the decidability of the forcing relation. *)

Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Prop3_Bi_Int_calcs.

Definition val_persist_R (W : Type) (val : W -> V -> Prop) R : Prop :=
  forall (w v : W), R w v -> (forall p, val w p -> val v p).

Definition R_refl {W : Type} (R : W -> W -> Prop) : Prop := forall (w : W), R w w.

Definition R_trans {W : Type} (R : W -> W -> Prop) : Prop := forall (u v w: W), R u v -> R v w -> R u w.

Fixpoint wforces W R (R_props : R_refl R * R_trans R) (val : W -> V -> Prop)
(pers : val_persist_R W val R) (w : W) (A : BPropF V) : Prop :=
  match A with
  | Var p => val w p
  | Bot _ => False
  | Top _ => True
  | And A B => (wforces W R R_props val pers w A) /\ (wforces W R R_props val  pers w B)
  | Or A B => (wforces W R R_props val  pers w A) \/ (wforces W R R_props val  pers w B)
  | Imp A B => forall v: W, R w v -> wforces W R R_props val  pers v A -> wforces W R R_props val  pers v B
  | Excl A B => exists v: W, (R v w) /\ wforces W R R_props val  pers v A /\ (wforces W R R_props val  pers v B -> False)
  end.

Definition mforces W R R_props val  pers (A : BPropF V) : Prop :=
  forall w : W, wforces W R R_props val  pers w A.

Definition valid_form A :=
  forall W R R_props (val : W -> V -> Prop)  pers, mforces W R R_props val  pers A.

Definition loc_conseq (Γ Δ : @Ensemble (BPropF V)) :=
  forall W R R_props (val : W -> V -> Prop)  pers (w : W),
    (forall A, (In _ Γ A) -> wforces W R R_props val pers w A) ->
    (exists B, (In _ Δ B) /\ (wforces W R R_props val pers w B)).

Definition glob_conseq (Γ Δ : @Ensemble (BPropF V)) :=
  forall W R R_props (val : W -> V -> Prop)  pers,
    (forall A, (In _ Γ A) -> mforces W R R_props val pers A) ->
    (forall (w :W), (exists B, (In _ Δ B) /\ (wforces W R R_props val  pers w B))).

Lemma Persistence : forall A W R R_props val  pers w, wforces W R R_props val pers w A ->
            (forall v, R w v -> wforces W R R_props val  pers v A).
Proof.
induction A ; intros ; try auto.
- simpl. unfold val_persist_R in pers. pose (pers w0 v).
  pose (v0 H0 w). apply v1. auto.
- simpl. split. inversion H. apply IHA1 with (w:=w) ; auto.
  inversion H. apply IHA2 with (w:=w) ; auto.
- simpl. inversion H. left. apply IHA1 with (w:=w) ; auto.
  right. apply IHA2 with (w:=w) ; auto.
- simpl. intros. simpl in H. apply H with (v:=v0) ; auto.
  destruct R_props. unfold R_trans in r0. apply r0 with (v:=v) ; auto.
- simpl. simpl in H. destruct H. destruct H. exists x. split. destruct R_props.
  unfold R_trans in r0. apply r0 with (v:=w) ; auto. assumption.
Qed.

(* Is this useful later on? Yes: in the proof of soundness and scompleteness. *)

Lemma wforces_dec : forall A W R R_props val  pers w,
    (wforces W R R_props val  pers w A) \/ ((wforces W R R_props val  pers w A) -> False).
Proof.
intros. apply classic.
Qed.