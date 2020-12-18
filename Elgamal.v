Require Import Lia Ring Field ZArith Znumtheory Zdiv Zpow_facts.
Open Scope Z_scope.

Section Encryption.

  Variables
    (p q k g t : Z)
    (p_prime : prime p) (q_prime : prime q)
    (H1 : 2 <= k) (H2 : p = k * q + 1)
    (H3 : 1 < t < p) (H4 : Zpow_mod t k p <> 1)
    (H5 : g = Zpow_mod t k p)
    (x h : Z) (* private key, public key *)
    (H6 : 1 < x < q) (H7 : h = Zpow_mod g x p). 

  Theorem p_pos : 0 < p. 
    pose (prime_ge_2 _ p_prime); lia.
  Qed.

  Theorem q_pos : 0 < q.
    pose (prime_ge_2 _ p_prime); lia.
  Qed.

  Print prime. 

  Theorem g_is_generator_of_subgroup_of_order_q : Zpow_mod g q p = 1.
  Proof.
    rewrite Zpow_mod_correct. 
    rewrite Zpow_mod_correct in H5.
    rewrite H5. rewrite <- Zpower_mod.
    rewrite <- Z.pow_mul_r.
    assert (Ht : k * q = p - 1) by lia.
    rewrite Ht.
    Check (Z.to_N p). (* rewrite the lemma below 
    assert (totient p = p - 1). 
    apply Euler_exp_totient. *)
    admit.
    
    lia. lia. lia.  lia. lia. 
  Admitted.

  Definition elgamal_enc (m : Z) (r : Z) :=
    (Zpow_mod g r p, Zmod (Zpow_mod g m p * Zpow_mod h r p) p).


  Definition elgamal_re_enc '(c1, c2) (r : Z) :=
    (Zmod (c1 * Zpow_mod g r p) p, Zmod (c2 * Zpow_mod h r p) p).


  Definition mult_ciphertext '(c11, c12) '(c21, c22) :=
    (Zmod (c11 * c21) p, Zmod (c12 * c22) p).

  Check euclid. 
  Print Euclid. (*
  Inductive Euclid (a b : Z) : Set :=
    Euclid_intro : forall u v d : Z, u * a + v * b = d -> Zis_gcd a b d -> Euclid a b *)

  Definition inverse (m : Z) : Z :=
    match euclid m p with
    | Euclid_intro _ _ u v d Huv Hgcd => u
    end.

  (* 
  Theorem tinv : inverse 2 3 = 2.
  Proof. 
    unfold inverse.
    simpl euclid. (* Nothing happens *)
  Admitted. *)
  
  (* This is going to be pain in the neck *)  
  Definition elgamal_dec '(c1, c2) :=
   Zmod (c2 * inverse (Zpow_mod c1 x p)) p. 

  
  
  


 

  
