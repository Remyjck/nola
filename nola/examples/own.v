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
(** The cmra could not be added directly as an argument to [cifs_own]
    for universe reasons. *)

Definition customCT A := Cifcon customCT_id (customCT_sel A)
(λ _, Empty_set) (λ _, Empty_set) (λ _, unitO) _.
(** [customC]: [customCT] registered *)
(*
    [inC : cifcon → cifcon → Type]
    To be understood as the inclusion of one custom constructor
    structure for [cif] into another.
*)
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
  Next Obligation (* Proof of non-expansiveness *). done. Qed.
End customC.
(** [customC] semantics registered *)
(*
    [inCS : ∀ (CON' CON : cifcon) (JUDG : ofe) Σ,
      inC CON' CON →
      Ecsem CON' CON JUDG Σ →
      Csem CON JUDG Σ → Prop]
    To be understood as the inclusion of the semantics.
*)
Notation customCS A := (inCS (customCT A)).

Section customC.
  Context `{inG Σ A, !customC A CON, !Csem CON JUDG Σ,
            !customCS A CON JUDG Σ}.

  (** Reify token *)
  #[export] Program Instance own_as_cif {γ} {a : A} :
      AsCif CON (λ _, own γ a)%I := AS_CIF (cif_own γ a) _.
  Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
End customC.

Class inA CON JUDG Σ A `{Csem CON JUDG Σ} : Type := A_OWN {
  own_inG :: inG Σ A;
  own_inC :: customC A CON;
  own_inCS :: customCS A CON JUDG Σ;
}.

From iris.heap_lang Require Import lang notation proofmode .

Section aProp_own.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  Local Notation aProp b := (aProp CON JUDG Σ b).

  Program Definition aProp_own `{inG Σ A, customC A CON, !customCS A CON JUDG Σ}
    γ (a : A) : aProp false :=
    FProp (λ _, own γ a)%I (cif_own γ a)%cif _.
  Next Obligation. intros. rewrite sem_cif_in /=. apply bi.wand_iff_refl. Qed.

  (* Context `{!inG Σ (authR max_natUR), customC (authR max_natUR) CON, !customCS (authR max_natUR) CON JUDG Σ}. *)
  (* Context `{!inG Σ (authR (optionUR (prodR fracR natR))), customC (authR (optionUR (prodR fracR natR))) CON, !customCS (authR (optionUR (prodR fracR natR))) CON JUDG Σ}. *)

  Context `{!inA CON JUDG Σ (authR max_natUR)}.
  Context `{!inA CON JUDG Σ (authR (optionUR (prodR fracR natR)))}.

  Let N := nroot .@ "counter".

  Notation own := aProp_own.

  Definition is_counter (v : val) (γ₁ γ₂ : gname) (n : nat) (q : Qp): aProp false :=
    (∃ (l : loc), ⌜v = LitV $ LitLoc l⌝ ∗ own γ₁ (◯ MaxNat n) ∗ own γ₂ (◯ Some (q, n)))%a.

End aProp_own.
