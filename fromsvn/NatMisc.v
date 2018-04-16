Require Import OrdersTac.
Require Import PeanoNat.

(* PeanoNat.Nat.add_0_r, PeanoNat.Nat.add_succ_r, ...
   are opaque, so we have to reprove them here       *)

Definition addSuccL (n m : nat) : S n + m = S (n + m).
Proof.
  reflexivity.
Defined.

Definition addSuccR (n m : nat) : n + S m = S (n + m).
Proof.
  induction n.
  - reflexivity.
  - rewrite (addSuccL n (S m)). rewrite IHn. reflexivity.
Defined.

Definition subDiag (n : nat) : n - n = 0.
Proof.
  induction n.
  - reflexivity.
  - exact (IHn).
Defined.

Definition leTrans (n m p : nat) 
         (nLem : n <= m) (mLep : m <= p) : n <= p.
Proof.
  induction mLep.
  + exact nLem.
  + exact (le_S _ _ IHmLep).
Defined.

Fixpoint subSuccL (n m : nat) (nLem : n <= m) : 
                  S m - n = S (m - n).
Proof.
  induction n.
  - induction m; reflexivity.
  - assert (forall l k : nat, (S l) - (S k) = l - k) 
    as dropS by reflexivity.
    induction nLem.
    + rewrite (dropS (S n) n).
      rewrite (dropS n n).
      rewrite (subSuccL _ _ (le_n n)).
      reflexivity.
    + assert (n <= m) as nLem'.
      * apply (leTrans _ _ _ (le_S _ _ (le_n n)) nLem).
      * rewrite (dropS (S m) n).
        rewrite (dropS m n).
        exact (subSuccL _ _ nLem').
Defined.

Definition lePlusL (n m : nat) : m <= n + m.
Proof.
  induction n.
  + exact (le_n m).
  + apply (leTrans m (n + m) (S n + m) IHn).
    exact (le_S _ _ (le_n (n + m))).
Defined.

Definition leNS {n m : nat} : n <= m -> S n <= S m.
Proof.
  intro nLEm.
  induction nLEm.
  - exact (le_n (S n)).
  - apply (leTrans (S n) (S m) (S (S m)) IHnLEm).
    exact (le_S _ _ (le_n (S m))).
Defined.

Definition le0n (n : nat) : 0 <= n.
Proof.
  induction n.
  - exact (le_n 0).
  - exact (le_S _ _ IHn).
Defined.

Definition leCases (n m : nat) : {c | c + n = m} + {c | n = c + m}.
Proof.
  induction n.
  - left. exists m. exact (PeanoNat.Nat.add_0_r m).
  - destruct IHn as [[d eq]|[d eq]]; destruct d.
    + right. exists 1. compute in eq. rewrite eq. trivial.
    + rewrite (addSuccL) in eq.
      left. exists d. rewrite (addSuccR). exact eq.
    + right. exists 1. compute in eq. rewrite eq. trivial.
    + rewrite (addSuccL) in eq.
      right. exists (S (S d)).
      rewrite (addSuccL). rewrite (addSuccL). 
      rewrite <- eq. trivial.
Defined.

Definition leDicho (n m : nat) : (n <= m) + (m < n).
Proof.
  destruct (leCases n m) as [[c eq]|[c eq]].
  - left. rewrite <- eq. exact (lePlusL c n).
  - destruct c.
    + compute in eq. left. rewrite eq. exact (le_n m).
    + right. rewrite eq. unfold "<". rewrite (addSuccL).
      apply leNS. exact (lePlusL c m).
Defined.

Definition ltCases (n m : nat) : (m = n)
                               + {c | (S c) + n = m} 
                               + {c | n = (S c) + m}.
Proof.
  induction n.
  - destruct m.
    + left. left. trivial.
    + left. right. exists m. exact (PeanoNat.Nat.add_0_r (S m)).
  - destruct IHn as [[eq|[d eq]]|[d eq]].
    + rewrite eq. right. exists 0. trivial.
    + rewrite <- eq. destruct d.
      * left. left. trivial.
      * left. right. exists d. rewrite ?addSuccR.
        rewrite ?addSuccL. trivial.
    + rewrite eq.
      right. exists (S d). rewrite ?addSuccL. trivial.
Defined.

Definition ltTricho (n m : nat) : (m = n) + (m < n) + (n < m).
Proof.
  destruct (ltCases n m) as [[eq | [c eq]]|[c eq]].
  - left. left. exact eq.
  - right. rewrite <- eq. unfold "<". rewrite addSuccL.
    apply leNS. exact (lePlusL c n).
  - left. right. rewrite eq. unfold "<". rewrite addSuccL.
    apply leNS. exact (lePlusL c m).
Defined.

Definition eqAddS {n m : nat} : (S n) = (S m) -> n = m.
Proof.
  inversion 1. trivial.
Defined.

Definition addComm (n m : nat) : n + m = m + n.
Proof.
  induction n.
  - rewrite (PeanoNat.Nat.add_0_r m). trivial.
  - rewrite (addSuccR). rewrite <- IHn. trivial.
Defined.

Definition nleSuccDiagL: forall n : nat, ~ S n <= n.
Proof.
  induction n; intro; inversion H; apply IHn.
  - rewrite H1; exact (le_n n).
  - exact (leTrans _ _ _ (le_S _ _ (le_n (S n))) H1).
Defined.

Definition leSN {n m : nat} : S n <= S m -> n <= m.
Proof.
  destruct (leCases (S n) (S m)) as [[d eq]|[d eq]]; destruct d.
  - compute in eq.
    rewrite (eqAddS eq). intro. exact (le_n m).
  - intro SnLeSm. inversion eq. rewrite (addSuccR d n).
    rewrite (addComm d n).
    assert (n + d <= S (n + d)).
    { exact (le_S _ _ (le_n (n + d))). }
    assert (n <= n + d).
    { rewrite (addComm n d). exact (lePlusL d n). }
    exact (leTrans _ _ _ H1 H).
  - rewrite (eqAddS eq). intro. exact (le_n m).
  - inversion eq. intro imp.
    apply False_rect.
    apply (nleSuccDiagL (d + S m)).
    apply (leTrans _ _ _ imp).
    exact (lePlusL d (S m)).
Defined.

Definition sub0R {n : nat} : n - 0 = n.
Proof.
  induction n.
  - trivial.
  - rewrite (subSuccL 0 n (le0n n)).
    rewrite IHn.
    reflexivity.
Defined.

Definition neqSucc0 (n : nat) : S n <> 0.
Proof.
  induction n; intro; discriminate H.
Defined.

Definition succPred {n : nat} : n <> 0 -> S (Nat.pred n) = n.
Proof.
  induction n.
  - intro NE00. apply False_ind. 
    assert (0 = 0) as E00 by trivial.
    exact (NE00 E00).
  - trivial.
Defined.

Definition le0eq0 (n : nat) : n <= 0 -> n = 0.
Proof.
  induction n.
  - trivial.
  - inversion 1.
Defined.

Definition leAntiSymmetric (n m : nat) : n <= m /\ m <= n -> n = m.
Proof.
  generalize m.
  induction n.
  + intro k.
    induction k. 
    * trivial.
    * intros [_ SLeZ]. inversion SLeZ.
  + intro k. induction k.
    * intros [SLeZ _]. inversion SLeZ.
    * intros [SNLeSK SKLeSN].
      assert (n <= k /\ k <= n) as NLeKLeN.
      { split.
        - exact (leSN SNLeSK).
        - exact (leSN SKLeSN). }
      pose (IHn k NLeKLeN) as NEqK.
      exact (f_equal S NEqK).
Defined.
