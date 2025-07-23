(** * Direct invariants *)

From nola.bi Require Export internal modw.
From nola.iris Require Export cif.
From nola.iris Require Export iprop.
From nola.iris Require Import sinv.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation.

Implicit Type (i : positive).

(** Ghost state for direct invariants *)
Class dinvGpreS Σ : Type := dinvGpreS_sinv : sinvGpreS Σ.
Local Existing Instance dinvGpreS_sinv.
Class dinvGS Σ : Type := dinvGS_sinv : sinvGS Σ.
Local Existing Instance dinvGS_sinv.
Definition dinvΣ:= sinvΣ.
#[export] Instance subG_dinvΣ
  `{!subG (dinvΣ Σ) Σ} : dinvGpreS Σ.
Proof. solve_inG. Qed.

Section dinv.
  Context `{!dinvGS Σ}.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Implicit Type Px : cif CON Σ.
  Import CsemNotation.

  (** [dinv_tok]: Direct invariant token *)
  Local Definition dinv_tok_def (Px : cif CON Σ) : iProp Σ :=
    ∃ i, sinv_tok i Px.
  Local Definition dinv_tok_aux : seal dinv_tok_def. Proof. by eexists. Qed.
  Definition dinv_tok := dinv_tok_aux.(unseal).
  Local Lemma dinv_tok_unseal : dinv_tok = dinv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [dinv_tok] is non-expansive *)
  #[export] Instance dinv_tok_ne : NonExpansive dinv_tok.
  Proof. rewrite dinv_tok_unseal. solve_proper. Qed.
  #[export] Instance dinv_tok_proper : Proper ((≡) ==> (⊣⊢)) dinv_tok.
  Proof. apply ne_proper, _. Qed.
  (** [dinv_tok] is persistent *)
  #[export] Instance dinv_tok_persistent {Px} : Persistent (dinv_tok Px).
  Proof. rewrite dinv_tok_unseal. exact _. Qed.
  (** [dinv_tok] is timeless for discrete formulas *)
  #[export] Instance dinv_tok_timeless `{!Discrete ⟦Px⟧ᶜ} : Timeless (dinv_tok Px).
  Proof. rewrite dinv_tok_unseal. exact _. Qed.

  (** World satisfaction *)
  Local Definition dinv_wsat_def (sm : iProp Σ -d> iProp Σ) : iProp Σ :=
    sinv_wsat (λ _, sm).
  Local Definition dinv_wsat_aux : seal dinv_wsat_def. Proof. by eexists. Qed.
  Definition dinv_wsat := dinv_wsat_aux.(unseal).
  Local Lemma dinv_wsat_unseal : dinv_wsat = dinv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [dinv_wsat] is non-expansive *)
  #[export] Instance dinv_wsat_ne : NonExpansive dinv_wsat.
  Proof. rewrite dinv_wsat_unseal. solve_proper. Qed.
  #[export] Instance dinv_wsat_proper : Proper ((≡) ==> (≡)) dinv_wsat.
  Proof. apply ne_proper, _. Qed.

  (** Allocate [dinv_tok] suspending the world satisfaction *)
  Lemma dinv_tok_alloc_suspend {sm} Px :
    dinv_wsat sm ==∗ dinv_tok Px ∗ (sm ⟦Px⟧ᶜ -∗ dinv_wsat sm).
  Proof.
    rewrite dinv_tok_unseal dinv_wsat_unseal. iIntros "W".
    iDestruct (sinv_tok_alloc_suspend Px with "W") as (I) "big".
    iMod ("big" $! (fresh I) with "[%]") as "[#inv →W]". { apply is_fresh. }
    iModIntro. iFrame "inv". iIntros "?". by iApply "→W".
  Qed.
  (** Allocate [dinv_tok] *)
  Lemma dinv_tok_alloc {sm} Px : sm ⟦Px⟧ᶜ =[dinv_wsat sm]=∗ dinv_tok Px.
  Proof.
    iIntros "? W". iMod (dinv_tok_alloc_suspend with "W") as "[$ →W]".
    iModIntro. by iApply "→W".
  Qed.

  (** Access the content of [dinv_tok] *)
  Lemma dinv_tok_acc {sm Px} :
    dinv_tok Px -∗ dinv_wsat sm -∗ sm ⟦Px⟧ᶜ ∗ (sm ⟦Px⟧ᶜ -∗ dinv_wsat sm).
  Proof.
    rewrite dinv_tok_unseal dinv_wsat_unseal. iIntros "[% i] W".
    iDestruct (sinv_tok_acc with "i W") as "[$$]".
  Qed.
  (** Access the content of [dinv_tok] for persistent propositions *)
  Lemma dinv_tok_acc_persistent {sm Px} : Persistent (sm ⟦Px⟧ᶜ) →
    dinv_tok Px -∗[dinv_wsat sm] sm ⟦Px⟧ᶜ.
  Proof.
    iIntros (?) "i W". iDestruct (dinv_tok_acc with "i W") as "[#Px cl]".
    iFrame "Px". by iApply "cl".
  Qed.
End dinv.

(** Allocate [dinv_wsat] *)
Lemma dinv_wsat_alloc `{!dinvGpreS Σ} :
  ⊢ |==> ∃ _ : dinvGS Σ, ∀ sm, internal_ne sm -∗ dinv_wsat sm.
Proof.
  iMod sinv_wsat_alloc as (γ) "W". iModIntro. iExists _. iIntros (?) "Ne".
  rewrite dinv_wsat_unseal. iApply "W". by iIntros.
Qed.
