From nola.examples Require Import aprop.
From nola.bi Require Import wpw.
From nola.examples Require Export con.
From nola.lrust Require Export notation proofmode.

Import WpwNotation CsemNotation ModwNotation.

About wpw.

Section awp.

  Context `{!Csem CON JUDG Σ, Jsem JUDG (iProp Σ)}.
  Context `{!lrustGS_gen hlc Σ}.
  Context `{!inv'GS (cifOF CON) Σ}.

  Local Notation "'aProp'" := (aProp CON JUDG Σ).


  About wp.

  Definition awp {b} s E e (Φ : _ -> aProp b) := wpw (inv_wsat ⟦⟧ᶜ) s E e%E (λ v, aProp_to_iProp_deriv der (Φ v)).
  Definition atwp {b} s E e (Φ : _ -> aProp b) := twpw (inv_wsat ⟦⟧ᶜ) s E e%E (λ v, aProp_to_iProp_deriv der (Φ v)).


  Lemma atwp_awp {b} s E e (Φ : _ -> aProp b) :
    atwp s E e Φ ⊢ awp s E e Φ.
  Proof.
    apply twpw_wpw.
  Qed.

End awp.