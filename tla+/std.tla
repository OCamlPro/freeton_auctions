---- MODULE std ----
    EXTENDS Integers

    min(i,j) == IF i < j THEN i ELSE j
    
    max(i,j) == IF i > j THEN i ELSE j

    Hash(i) == i
====