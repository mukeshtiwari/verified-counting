Require Import Lia Ring Field ZArith Znumtheory Zpow_facts.

Open Scope Z_scope.

Section Encryption.

  Variables
    (p q k : Z)
    (H0 : prime p) (H1 : prime q)
    (H2 : 2 <= k) (H3 : p = k * q + 1)


    


