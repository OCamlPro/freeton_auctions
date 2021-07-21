pragma ton-solidity >=0.44;

import "IConstants.sol";

interface IAuction is IConstants {

    // Starts the bid process
    function bid(uint256) external;

    // Validates a bid.
    // This can only be called by a BidBuilder contract
    function validateBid(Bidder) external;
    
    // Ends an auction if it is in a final state.
    function endAuction() external;
}