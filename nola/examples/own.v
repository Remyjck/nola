From nola.iris Require Import cif.
From iris.base_logic.lib Require Import own.
From nola.examples Require Import aprop.

Implicit Type Σ : gFunctors.

(** ** Custom constructors *)

(** [customCT]: Constructor *)
Variant customCT_id := .
Variant customCT_sel (A : cmra) :=
| (** Ownership token *) cifs_own (γ : gname) (a : cmra_car A).
Arguments cifs_own {_} _ _.
Set Printing Universes.

Definition customCT A := Cifcon customCT_id (customCT_sel A)
(λ _, Empty_set) (λ _, Empty_set) (λ _, unitO) _.
(** [customC]: [customCT] registered *)
Notation customC A := (inC (customCT A)).
Section customC.
  Context `{!customC A CON} {Σ}.
  (** [cif_own]: Own token *)
  Definition cif_own γ a : cif CON Σ :=
    cif_in (customCT A) (cifs_own γ a) nullary nullary ().

  (** Semantics of [customCT] *)
  Definition customCT_sem `{inG Σ A} (s : customCT_sel A) : iProp Σ :=
    match s with
    | cifs_own γ a => own γ a
    end.
  #[export] Program Instance customCT_ecsem `{inG Σ A} {JUDG}
    : Ecsem (customCT A) CON JUDG Σ :=
    ECSEM (λ _ _ s _ _ _, customCT_sem s) _.
  Next Obligation. done. Qed.
End customC.
(** [customC] semantics registered *)
Notation customCS A := (inCS (customCT A)).

Section customC.
  Context `{inG Σ A, !customC A CON, !Csem CON JUDG Σ,
            !customCS A CON JUDG Σ}.

  (** Reify token *)
  #[export] Program Instance own_as_cif {γ} {a : A} :
      AsCif CON (λ _, own γ a)%I := AS_CIF (cif_own γ a) _.
  Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
End customC.

Section aProp_own.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Context `{inG Σ A, customC A CON, !customCS A CON JUDG Σ}.
  Context `{inG Σ B, customC B CON, !customCS B CON JUDG Σ}.

  Program Definition aProp_own γ (a : A) : aProp CON JUDG Σ false :=
    FProp (own γ a)%I (cif_own γ a)%cif _.
  Next Obligation. intros. by rewrite sem_cif_in /=. Qed.

  Program Definition aProp_own' γ (a : B) : aProp CON JUDG Σ false :=
    FProp (own γ a)%I (cif_own γ a)%cif _.
  Next Obligation. intros. by rewrite sem_cif_in /=. Qed.

End aProp_own.


