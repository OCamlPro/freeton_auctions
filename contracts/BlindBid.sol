pragma ton-solidity >=0.44;

import "Bid.sol";
import "Hasher.sol";

// A blind bid is a bid with an additional function: reveal.
contract BlindBid is Bid, Hasher {

    // Replaces the commitment by the actual amount.
    // Once the commitment has been revealed, the usual bid verification process 
    // can start.
    function reveal(uint256 salt, uint256 amount) public{
        require (msg.sender == s_bid_builder || msg.sender == s_bidder, E_UNAUTHORIZED);
        tvm.accept();
        require (s_commitment == hash(salt, amount), E_INVALID_BID);
        s_commitment = amount;
        emit RevelationSuccess();
    }

}