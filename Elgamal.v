Require Import Lia Ring Field ZArith Znumtheory Zdiv Zpow_facts.
Require Import Coqprime.PrimalityTest.Zp.
Require Import Coqprime.Z.Pmod.
Require Import Coqprime.elliptic.GZnZ.
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

  Check znz p.
  Check add.
  Check inv.
  
  
  Theorem p_pos : 0 < p. 
    pose (prime_ge_2 _ p_prime); lia.
  Qed.

  
  Theorem q_pos : 0 < q.
    pose (prime_ge_2 _ p_prime); lia.
  Qed.

  
  Lemma lt_1_p : 1 < p.
  Proof. lia. Qed.
  
  
  Lemma mod_p_order : Coqprime.PrimalityTest.FGroup.g_order (Coqprime.PrimalityTest.Zp.ZPGroup p lt_1_p) = p - 1.
  Proof.
    intros; rewrite <- Coqprime.PrimalityTest.Zp.phi_is_order.
    apply Coqprime.PrimalityTest.Euler.prime_phi_n_minus_1; auto.
  Qed.
  
  
  Lemma fermat_little: forall a (a_nonzero : a mod p <> 0),
      a ^ (p - 1) mod p = 1.
  Proof.
    intros ? Ha.
    assert (rel_prime a p).  {
      apply rel_prime_mod_rev. apply p_pos.
      apply rel_prime_le_prime; auto.
      assert (0 <= a mod p < p).
      eapply Z.mod_pos_bound. apply p_pos. 
      lia. 
    }
    assert (0 <= p-1). lia. 
    pose proof (Coqprime.PrimalityTest.Zp.Zpower_mod_is_gpow a (p-1) p lt_1_p H H0).
    rewrite H8. rewrite <- mod_p_order.
    apply Coqprime.PrimalityTest.EGroup.fermat_gen; try (apply Z.eq_dec).
    apply Coqprime.PrimalityTest.Zp.in_mod_ZPGroup; auto. 
  Qed.
    
   
  Theorem g_is_generator_of_subgroup_of_order_q : Zpow_mod g q p = 1.
  Proof.
    rewrite Zpow_mod_correct. 
    rewrite Zpow_mod_correct in H5.
    rewrite H5. rewrite <- Zpower_mod.
    rewrite <- Z.pow_mul_r.
    assert (Ht : k * q = p - 1) by lia.
    rewrite Ht.
    apply fermat_little. 
    apply Zrel_prime_neq_mod_0. lia.
    assert (rel_prime t p). {
      apply rel_prime_le_prime. auto. lia.
    } assumption. lia. lia. lia. lia. lia.
  Qed.

  Compute Zegcd 2 3.
  Compute (Zmod (-1) 3).
  
  (* m : Zmod p, r : Zmod q *)
  Definition elgamal_enc (m : Z) (r : Z) :=
    (Zpow_mod g r p, Zmod (Zpow_mod g m p * Zpow_mod h r p) p).


  Definition elgamal_re_enc '(c1, c2) (r : Z) :=
    (Zmod (c1 * Zpow_mod g r p) p, Zmod (c2 * Zpow_mod h r p) p).


  Definition mult_ciphertext '(c11, c12) '(c21, c22) :=
    (Zmod (c11 * c21) p, Zmod (c12 * c22) p).

  

  Compute (Zpow_mod 100 0 47).
  Definition inv (m : Z) : Z :=
    match Zegcd m p with
    | (u, _, _) => Zmod u p
    end.

    
  Definition elgamal_dec '(c1, c2) :=
   Zmod (c2 * inv (Zpow_mod c1 x p)) p. 
  
End Encryption.


  
  


 

  
