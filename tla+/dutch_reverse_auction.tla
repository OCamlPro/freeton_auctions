---- MODULE dutch_reverse_auction ----

    EXTENDS Integers

    CONSTANTS 
        starting_price, (* The auction starting price *) 
        limit_price, (* The minimal price the seller will accept *)
        price_delta, (* The price decrement for each tick*)
        time_delta

    VARIABLES 
        finished, (* TRUE,buy_value if the object has a buyer  *)
        time, (* time *)
        current_price_var (* Useless variable, used for readable cexs *)

    vars == <<finished, time, current_price_var>>

    min(i,j) == IF i < j THEN i ELSE j
    max(i,j) == IF i > j THEN i ELSE j

    current_price ==
        IF finished[1]
        THEN finished[2]
        ELSE
          LET delta == time \div time_delta IN
          min(starting_price + delta * price_delta, limit_price)

    Init == 
        /\ starting_price < limit_price
        /\ finished = <<FALSE,0>>
        /\ time = 0
        /\ current_price_var = starting_price

    time_has_passed == 
        \/ finished[1]
        \/ (
            /\ current_price = limit_price
            /\ (time + 1) % time_delta = 0
           )

    time_passes == time' = time + 1

    bid == 
        /\ finished'= <<TRUE, current_price>>
        /\ UNCHANGED current_price_var
    
    no_bid == 
        /\ UNCHANGED finished
        /\ IF (time' % time_delta = 0)
           THEN 
             current_price_var' = 
             min(limit_price, current_price_var + price_delta)
           ELSE 
             UNCHANGED current_price_var
    
    Next == 
        IF time_has_passed
        THEN UNCHANGED vars 
        ELSE /\ time_passes
             /\ \/ no_bid
                \/ bid

    type_check ==
        /\ finished[1] \in {TRUE,FALSE}
        /\ finished[2] \in Int
        /\ current_price_var = current_price
    
    test == <>(finished[1])
====