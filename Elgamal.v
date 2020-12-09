Require Import Lia Ring Field ZArith Znumtheory Zdiv Zpow_facts.
Open Scope Z_scope.

Section Encryption.

  Variables
    (p q k g r : Z)
    (p_prime : prime p) (q_prime : prime q)
    (H4 : 2 <= k) (H5 : p = k * q + 1)
    (H6 : 1 < r < p) (H7 : Zpow_mod r k p <> 1)
    (H8 : g = Zpow_mod r k p).

  Theorem p_pos : 0 < p.
    generalize (prime_ge_2 _ p_prime); lia.
  Qed.

  Theorem q_pos : 0 < q.
    generalize (prime_ge_2 _ p_prime); lia.
  Qed.
  

  Theorem g_is_generator_of_subgroup_of_order_q : Zpow_mod g q p = 1.
  Proof.
    rewrite Zpow_mod_correct. 
    rewrite Zpow_mod_correct in H8.
    rewrite H8. rewrite <- Zpower_mod.
    rewrite <- Z.pow_mul_r.
    assert (Ht : k * q = p - 1) by lia.
    rewrite Ht.
    
