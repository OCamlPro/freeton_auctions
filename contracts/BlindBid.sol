pragma ton-solidity >=0.44;

import "Bid.sol";
import "Hasher.sol";

contract BlindBid is Bid, Hasher {

    function reveal(uint256 salt, uint256 amount) public{
        require (msg.sender == s_bid_builder || msg.sender == s_bidder, E_UNAUTHORIZED);
        tvm.accept();
        require (s_commitment == hash(salt, amount), E_INVALID_BID);
        s_commitment = amount;
        emit RevelationSuccess();
    }

}